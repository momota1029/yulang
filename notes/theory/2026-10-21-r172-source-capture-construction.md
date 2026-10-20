# R172 source-directed terminal Capture construction — revision 2

Status: **UNREVIEWED correction; source-to-Origin attribution UNKNOWN; all parent gates OPEN.**
Author: `/root/r172_source_capture_proof`; no coauthors or descendants.
Assignment `R172-SOURCE-CAPTURE-CONSTRUCTION`, sequential result revision **2** under the
unchanged R172 contract revision 1. Luna requested this repair after fresh independent
review. No compiler/query changes or execution are included.

## Current result and correction

Revision 1 overclaimed that equal branded ConstraintOccurrenceIds authenticate a queried
Origin as the direct source drain. That assertion in historical §§2 and 5, and its repeated
handoff assertion, is **withdrawn**. The source store provenance still authenticates the
source cause→FactId→exact Terms. Occurrence equality selects candidate Origins; it does
not authenticate which typed drain created a candidate or whether its seed was used.

The exact owner distinction is visible at `lib::start_typed_drain:12274–12289`:

```rust
let seed = self.candidate_context_seed_with_formal(item.task, occurrence, inferred_entry, formal)?;
item.relation = item.relation.or(seed);
```

The direct source caller supplies `relation: None`, so on its successful path the source
task creates a seed and uses that seed. This proves **static direct-seed existence** for
the source construction. It does not give a retained event certificate identifying that
particular direct drain among all observed Origins for the same occurrence.

`candidate_context_step_replay_child` independently builds a TypedWorkItem with the Replay
operation's task, `relation: Some(replay_child)` and replay acknowledgement, then calls
the same `start_typed_drain` with the inherited occurrence/cause. That call creates another
Origin for its newly computed seed even though `.or(seed)` keeps the pre-existing Replay
relation. Therefore both direct and Replay-created seed records can carry the exact same
occurrence/cause key; the Replay task need not be the original source fact's task.

The retained `Origin` fields are relation, occurrence, optional inferred_entry and optional
formal. For the annotated Computation witnesses at issue, the optional handles supply no
retained discriminator for direct-source versus Replay seed creation or seed disposition.
The transient drain's task/acknowledgement distinguishes the calls while it exists; this
packet has not established a persistent source FactId/Terms→that direct-drain event→used
seed certificate after drain completion. Relation interning and endpoint equality do not
restore event ownership. This is an **unestablished attribution**, not a proof that every
possible construction-directed recovery is impossible.

## Parent application and exact remaining premise

The original parent, quantifiers, source domain and contract remain those recorded in the
historical revision below. Its source slot facts remain established at their original
admission owners. The Link30→module root→Capture→own FreshUse→callee route→A_F demand spine
remains a candidate static construction to audit. Any historical assertion that occurrence
matching completes source-seed ancestry, or thereby authenticates all four source witnesses
at Capture/q_F, is superseded by this revision. The finite level argument alone does not
repair this attribution. No concrete same-provider source/native association is closed.

`R172-PROOF-QUERY-1` now requires an additional, independent component:
**direct_source_drain_attribution=UNKNOWN** until retained owner evidence identifies the
direct source task, its used seed and their source receipt, rather than just a key match.
Complete enumeration of facts and occurrence-matching Origins proves enumeration coverage
only. Neither completeness boolean can certify this attribution or authorize a dependent
probe. Preserve all candidate Origins, Derived/Transport/ordered Replay alternatives,
self-pair factorizations, shared-anchor routes and residual/scoped payloads.

First owner requiring discrimination: `start_typed_drain` seed creation versus selection,
with provenance from its direct-source or Replay caller. Minimal evidence needed is the
source receipt's exact task and a retained construction/event association to the selected
seed, including whether the incoming item already carried a relation/replay owner. This is
a specification of missing evidence, **not** an authorization to retain new compiler state.
Luna owns any further construction proof, revised lease or implementation decision.

Attribution falsifier: an occurrence-matching Origin created for a Replay operation task
is accepted as the original fact's direct source seed merely because the occurrence/cause
matches. An authenticated attribution must distinguish this case using owning evidence.
No source-qualified semantic counterexample follows from this bookkeeping limitation.
R169 source incidence, R70/R71/R165/R166/Replay, original A/B, F1/FK1 and production remain OPEN.

## Revision receipt and cessation

Historical revision 1 note bytes are preserved verbatim after the marker below; their
SHA-256 is `2a180a3142d038f523c6d400f849b68e3429204cad9710a443d4a18f952343d6`.
Historical handoff revision 1 SHA-256 is
`09d49081e3ce39b4253a77369ce2a567d20ae68aa8f4c186963bc02b4da2dfaa`.
Only this note and the exact proof handoff are revised. Checks are bounded static reads of
the seed and Replay constructors and SHA-256 validation. No tests/build/probe/compiler,
code/query writes, Git, descendants, scratch/generated paths or background work. Requested
Sol/high; observed model/effort UNKNOWN/UNKNOWN. No new resource grant or carryover is
claimed. Writes stop with the revision 2 handoff; fresh review belongs to Luna.

---

**HISTORICAL REVISION 1 — superseded as specified above; not current proof authority.**

<!-- BEGIN BYTE-PRESERVED R172 NOTE REVISION 1 -->
# R172 source-directed terminal Capture construction

Date: 2026-10-21 repository session. **UNREVIEWED source/native construction result; original parents OPEN.**
Author: `/root/r172_source_capture_proof`; no coauthors or descendants.
Assignment `R172-SOURCE-CAPTURE-CONSTRUCTION`, result revision 1. Contract revision 1:
`tasks/agent-loop/sprints/source-fact-capture-construction-20261021-r172.md`, SHA-256
`4d0976759a061241244b06f0eb2ca1c6960f9feb02989eaa73b205e0fd9f108c`.
Luna's current-session activation is the authority; the frozen prospective contract's
CANDIDATE header is not a second runtime receipt. Baseline supplied by Luna: `e6ffba08c`.

## 1. Result and immediate parent application

The parent is `2026-10-15-computation-forwarding-preservation.md` §§1,6–7. Preserve original
resolved declarations/formals, one shared satisfying assignment, open incoming E, arbitrary
finite forwarding chains, repeated calls, simultaneous entries and all finite prefixes.
This packet treats only the first `terminal` instance compared inside the original `relay`
body of the unchanged R171 fixture. It changes none of those parent quantifiers.

The source-directed construction below identifies a concrete route through the actual
owners, including the previously implicit **definition-final Link slot 30** between the
Lambda's expression root and its module provider root. It derives how all four required
source witnesses reach the same terminal Capture and its own FreshUse, then the exact
forwarding Apply's Function comparison. This is a static finite-instance construction,
not an observation of numeric FactId/RelationId values or an independently reviewed theorem.
The successful frozen R171 inference receipt supplies successful execution of this fixed
default candidate path; its capped observer does not authenticate the source keys themselves.

Applied to §6: for this first original-relay comparison, the construction supplies the
specific producer route that must authenticate the terminal instance map. Once its exact
source-keyed owner query is authenticated, the existing instance-relative implication
yields `e_nR <= mu_T(e_tT) <= mu_T(e_nT) <= mu_T(e_RT) <= e_C <= e_AF`.
Relay's original Name equality and Lambda slot 4 then give `e_tR <= e_RR` for that original
relay template. No inference from this route establishes the later copied-relay-to-answer
join, the universal mapped-admission premise, dynamic entry/read/Force, or Replay residual
coverage. `R169-SOURCE-FACT-CAPTURE-INCIDENCE-1`, R70/R71/R165/R166/Replay and original A/B remain
OPEN pending owner-query authentication and independent review. No production authority follows.

## 2. Exact selections from original source facts

Reuse R171's CLEAN-reviewed source membership proof, not the spelling `t` alone. Let L_T be
terminal's original Lambda `[37,69)`, N_T its complete body Name `[68,69)`, and D_T its original
resolved declaration. Let A_F be relay's original Apply `[98,108)`, with module callee Name
`terminal` `[98,106)` and whole argument Name N_R `[107,108)` resolving to relay's own formal.
These are byte locators into fixture SHA-256
`cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`, not invented HIR ordinals.
All selections below use the branded HIR occurrences produced for those exact operands.

For a source occurrence X and slot s, write `o(X,s)=ConstraintOccurrenceId::new(X,s)` and
`c(X,s)=CauseId::for_occurrence(o(X,s))`. The exact source store fact is selected by the
retained provenance edge with that cause, then its FactId, then that fact's stored Terms.
FactId is not guessed from allocation order. Duplicate Term pairs may share FactId while
their causes remain distinct. The table specifies actual constructor operands:

| Source key | Stored lower/upper Terms, as constructed | Owning admission |
| --- | --- | --- |
| o(L_T,2) | P_T / Lambda expression root component | `lib::admit_lambda_fact` |
| o(N_T,1) | live positive registered e_tT / live negative Name e_nT | `candidate_formal_effect_equal` |
| o(N_T,2) | live positive e_nT / live negative e_tT | same call, second offset |
| o(L_T,4) | live positive body e_nT / live negative fresh Lambda e_RT | `admit_lambda_fact`, body slot |

P_T is the exact positive Function Term returned by that Lambda admission; its AE is the
registered e_tT, RE is the freshly allocated e_RT, and result is the actual formal Value
endpoint. The Int annotation does not replace that result by a positive Int leaf.
Computation role skips slot 3. No omitted-formal FormalConstruction handle is required.

`admit_and_record_provenance` returns the actual FactId after retaining cause→fact;
both Lambda slots and FormalName equality call it before their live drains. At
`start_typed_drain`, `candidate_context_seed_with_formal` calls `candidate_context_seed`
with that exact occurrence. The latter retains `Origin { occurrence, relation, ... }`
after canonicalizing the actual task pair. Therefore source store and context origin are
joined by the same branded occurrence, even though Origin has no redundant FactId field.
Select **all** Origins for the key; neither relation interning nor FactId dedup proves a
unique construction event. The absence of FactId inside Origin is not an absent association.

## 3. Forward construction to terminal's own Capture

The changed method starts with those source admissions and follows their construction;
it never starts with a conveniently shaped FunctionPort row.

The unchanged fixture has no nested Block/initializer. `candidate_source::Work::Visit`
starts each definition at level 1 and visits Lambda bodies at the same level. Component
and parameter level initialization therefore places e_tT, e_nT, e_RT and the relevant
Value roots at level 1. Formal Int annotation creates no deeper effect row or effect
allowance; concrete `[signal]` is local permission and does not cap incoming E.
The default `CandidateInference::solve` mode used by R171 does not enable scoped_experiment.

Before terminal's first incoming use, its source contains only the formal annotation,
resolved formal Name, Lambda and definition-final link. Freshly allocated terminal effect
rows are distinct. Ordinary same-level row bounds do not equate them: extrusion's Visit
branch returns the existing endpoint when `original_level <= target`; no parent/copy pair
is created on this interval. `settle_candidate_intrusion` merges only pending actual
extrusion-parent records, so the two-way Name bounds alone do not collapse these rows.
Consequently the required original Name/body constraints here are non-self physical bounds.
This is a property of this finite initial interval, not an assumption for later uses or
the parent's general source domain.

The exact construction spine is:

1. Lambda slot 2 admits `P_T <= r_LT`. Its structural bound is installed by
   `candidate_apply_value`/`candidate_insert_bound_with_evidence`; the admission retains
   the processing relation, and `candidate_context_bound_for` retains its Derived edge
   and attaches its precise `(owner,side,item)` key. Physical emission retains the
   addressed vector slot and immediate readback.
2. The definition-final `Action::Link`, source key **o(L_T,30)**, admits `r_LT <= r_DT`.
   It is emitted at `candidate_source:1540`, executed by `admit_candidate_value_link`,
   and is distinct from Lambda slot 2. Thus r_LT and the module root r_DT must not be
   silently identified. Ordinary bound replay composes the positive provider bound with
   this upper bound, retaining ordered `(lower,upper,lower_input,upper_input)`, and
   propagates P_T to the module root's positive fiber.
3. `execute_candidate_graph_plan` finishes the dependency-first terminal schedule before
   exposing its graph. Its target position is D_T's DefinitionOrderId and capture begins
   at D_T's actual live module root, boundary 0. Those level-1 rows are local. Capture
   traverses the root's actual nonvariable positive bound P_T and P_T's ordered children.
4. The AE child reaches e_tT. `expand_row` traverses its actual upper bound to e_nT;
   e_nT's upper fibers include the reverse Name bound and body slot 4 to e_RT. The RE
   child also reaches e_RT. All three source effect witnesses are therefore reachable
   from this same provider capture, rather than borrowed from a sibling graph.
5. For each encountered physical bound, `Capture::bound` obtains its raw BoundKey cursor
   **before interning** endpoints, iterates every attached relation, and retains each
   relation plus that raw key and its exact EvidenceSnapshot. It does not select one
   canonical relation by endpoint equality. These attachments retain the source-seed
   ancestry through the preceding Derived/Replay records. Evidence coverage gap bits
   remain honest; the snapshot alone is not a complete source or Replay proof.

This gives a forward construction for the source→provider-Capture join on this initial
interval. R171's output is compatible comparison evidence: route 0 printed P-Term 265
under a module root and the three raw effect keys 12→1, 1→12 and 1→14. Those numbers are
**not used to identify** terminal's source facts, their e_t/e_n/e_R roles, the module use
or q_F. They cannot replace the source-key selection and owner spine above.

## 4. Own map and exact forwarding consumer

A_F's callee source Name resolves to D_T. Its `Action::Module` forms the artifact-branded
DefinitionUseId from that exact Name occurrence. `validated_route_use` checks its own
DefinitionUseCause. The resolved record retains D_T as target, relay as parent and the
callee's own use component. `route_candidate_graph` takes D_T's stored live_root/boundary,
recaptures that actual graph and supplies it to `instantiate_candidate_graph`.

`prepare_candidate_fresh_use` allocates one context_use and one canonical-row map for this
route. Every Function child is reconstructed from the same graph nodes and terms vector;
each captured bound uses these same mapped nodes. Here the captured level-1 generic rows
are freshened at the caller's level 1, and distinct source rows remain distinct map inputs
on this interval. `begin_candidate_fresh_bound` retains the source BoundKey, imported
snapshot, own context_use, exact mapped relation and own context/scoped/evidence maps.
`freshen_candidate_graph_core` drives each bound restoration before returning the mapped
root. Its ordinary source→map path is not another module's or the demand's map.

`instantiate_candidate_graph` calls `route` on that same DefinitionUseId. This admits the
mapped root→callee Name fact; RoutedUseProvenance retains its FactId and use_id. The fresh
positive Function flows through that root/Name bound to A_F's own callee component.
Separately, the A_F Apply recipe retains its exact callee and argument components.
`shadow_apply::admit_candidate` authenticates those against ApplySourceInput and retains
NativeInterface: AE is N_R's effect; demand and invocation RE are that Apply's own Terms.
A_F slot 0 admits this callee component against **that demand**.

The provider lower fiber and A_F upper-demand fiber meet by actual ordered Replay. Define
q_F to be every resulting retained relation whose positive provider is the reconstructed
P_T from this authenticated terminal route and whose negative Function is this exact
NativeInterface.demand, with the corresponding source route/Apply ancestry. This definition
does not name q=27,77,95 from R171 or infer identity from a matching endpoint alone.
`candidate_function_port_admit` retains FunctionPort(parent=q_F,field,child): AE uses Swap,
RE uses Preserve. It uses q_F's post-check context, prefixes child-local wrappers in source
order and preserves source/scoped payload. Thus the resulting child comparisons are the
actual `e_nR <= mu_T(e_tT)` and `mu_T(e_RT) <= e_C`. A_F slot 2 supplies `e_C <= e_AF`.

In this first default-mode interval contexts are identity and scoped payload is default;
the constructors still retain ordered Replay alternatives. This does not prove that the
general post-check residual equals an unconsumed context. All Derived, Transport and Replay
alternatives must be preserved by the query. Replay interning of an identical dependency
is not uniqueness of an operation, use or source event.

## 5. Authentication boundary, absent records and falsifier

The construction is not a frozen numerical tuple: the R171 observer deliberately reports
`NotJoinedToContextRecord`, truncates its row selection and some individual records, and
prints no store source CauseId/FactId/Terms keyed to L_T/N_T/A_F. The first missing evidence
in that **observation** is source-key→store provenance→Origin selection at
`ordinary_provider_observation`; the producing owners do retain this association.
It would be incorrect to claim an absent compiler supplier merely because that observer
does not borrow it. R172's leased source-keyed borrowed query is the immediate discriminant.

For more general histories, Capture::intern canonicalizes before keeping its node, Row
retains representative/local only, and requested→capture representative plus historical
freshening observations and forest snapshots are cfg(test). A present raw Bound.source_bound
and ordered original-Function/graph child traversal can still authenticate a positive
path. Therefore absent historical observations do not refute this initial construction or
justify skipping existing raw/Transport/shared-anchor alternatives. If later representative
changes make a required original→graph-row choice ambiguous and no retained positive path
resolves it, return that component UNKNOWN at Capture::intern/row or fresh-use row mapping;
do not reconstruct the old alias partition from current representative equality.

Canonical self-pairs require their own factorization: source cause/fact/Terms and original
relation; authenticated same-provider original→graph→own-map rows; unchanged endpoint or
retained transport alternative; current residual/scoped payload. `candidate_apply_effect`
returns before physical admission on a canonical self-pair. Missing physical emission then
proves neither witness loss nor successful preservation. Nonlocal rows similarly require
their actual shared session anchor and same-consumer route. These branches are not used to
erase a missing source witness and are not proved universally by the distinct-row interval.

**Exact falsifier for this proposed finite association:** the source-keyed query selects
the four original successful terminal facts and their source Origins, yet terminal's own
authenticated Capture/use route fails the forward construction above; or its own ordered
node maps disagree with their original Function/Name/body operands; or no authenticated
Replay path reaches the A_F NativeInterface demand with the claimed payload. A matching
numeric row, differing q values, coverage gaps alone, a missing optional handle, truncated
output or absent self-pair emission is insufficient. Failure of a required join must name
the first constructor and retained inputs, and preserve every alternative before concluding
absence. No such source-qualified counterexample has been established here.

Mutual TODO `R172-PROOF-QUERY-1`, owner Luna: freeze source-query code and the exact structured
join result for L_T2/N_T1/N_T2/L_T4, D_T's own module route and A_F's native consumer. Required
evidence is the actual provenance/Origin/Capture/map/dependency owner join above, with
per-component completeness. If it is incomplete, stop without running a nondiscriminating
probe. Any historical certificate retention or changed compiler owner requires a new grant;
this proof packet does not authorize code writes or a larger source domain.

## 6. Frozen dependencies and checks

Reused only within their real premises: R171 occurrence-qualified source membership and
initial operation derivation; parent's original-template lemma and instance-relative
implication; R169 direct source-drain supplier. R165 applies only after a captured fiber is
identified, R70 only under ENTRY-WF, and R71 only forward raw→canonical. They do not prove the
inverse source join. Source/runtime RootComp preservation is not replaced by this finite
native constraint construction. F1/FK1 and foreign continuation quantifiers remain independent.

Validated SHA-256 inputs (compiler owners: repository authors; fixture/harness/probe:
Luna; R171 proof: its recorded leaf author). Code hashes pin the baseline bodies read
before Luna's independent R172 borrowed-query edits; that provisional API is not consumed
as proof evidence here. The final combined code/query snapshot requires Luna's own freeze
and independent review:

```text
contract          4d0976759a061241244b06f0eb2ca1c6960f9feb02989eaa73b205e0fd9f108c
parent            d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79
R171 source       d19b5ceb2c1ace95ce2cc49bdd6c35ef4bd4de223f07e181a472a037a35a133b
R171 native       a57e2b3aa012251d99a34f1dab42894a9c2ed76541b1e51ddc7c8526b6b3f147
fixture           cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f
R171 stdout       5c47875a6bdb59da380772df81660ec71ac59b9317030de149e26599c883fff5
candidate_context d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb
candidate_scheme  9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225
shadow_apply      46959cf65e447f4c1dc3db34f1969cfa5746e8d7b86227b1b8b456ac2701ddbb
candidate_source  cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7
candidate_effect  c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1
candidate_extrusion 7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332
candidate_intrusion 475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97
solver lib        c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985
HIR local_source  d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442
```

Checks: static source/authority reading, original source operand specialization, constructor
and ordered dependency audit, SHA-256 validation. No tests/builds/compiler/probes/Y2/Y3/
evaluator/Git/network, user/external contact or descendants. Some broad early captures hit
output limits; relied-on constructors were reread in bounded excerpts. No scratch or
generated paths. Requested prover routing Sol/high; observed model/effort UNKNOWN/UNKNOWN.
1200 seconds fully charged, no carryover; exact observed launch-to-stop elapsed UNKNOWN.
Only this note and the exact proof inbox path are written. Fresh independent review and
source-query intake belong to Luna. Writes stop with the frozen handoff; no background work.
