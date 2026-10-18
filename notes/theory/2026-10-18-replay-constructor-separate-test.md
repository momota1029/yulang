# Separate rejected Replay observation: source correspondence draft

Status: **DRAFT, conditional source derivation; not frozen or independently reviewed**.
Author: `/root/replay_constructor_separate_proof_20261018`; no coauthors or descendants.
Requested Sol/high; observed model UNKNOWN, effort UNKNOWN.
Sprint `npair-replay-constructor-lineage-20261018-r4`, revision 4,
SHA-256 `1eed76f1c8d9f9fb115a1f2a26a9845da230e7c17762cf3350d691190f43c049`.
Source-only preparation began 2026-10-18 02:59:58 UTC. Proof allocation 180s,
Astra 0; waiting time is not evidence of active proof work.

## Parent and exact application

`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` asks for the authentic negative
formal pair, ordinary formal edges and contribution/permission association
through `f () -> install(g) -> fresh local use -> g ()`. Preserve fixed `c`,
every original provider, assignment, context, world, occurrence, typed position,
guard, continuation, interaction, Call demand and future at its original scope.
J1/J2, initializer effects, permission/inflow/residual and provider/witness/use
lineages remain distinct. F1 and FK1 are independent obligations. Parent **OPEN**;
original-condition closure **0 -> 0**.

This draft supplies a source-grounded decision procedure for the row-map portion
of one specimen. It does not yet decide whether this join is shared or loses
fresh separation. The first missing input is the fresh-reviewed observation of
the new exact test, owned by the implementation author and Luna's runtime lane.
Authentication returning None proves neither ownership alternative.

Governing authority is the 2026-10-11 inference principles §§1/1.1 and the
2026-10-17 adoption receipt selecting NPAIR proposal §§2–4. Ordinary generation,
accumulation, propagation, levels, extrusion, qualifying Value-SCC intrusion and
generalization remain required. N-Transport and N-Subtract-Elim are obligations,
not consequences of adopting their definitions. The native implementation
contract's reviewed L1 and local L2 remain usable only within their premises;
its missing whole-presentation J2 map and limited L4 allocation fact remain so.

## C1. Capture classification and its observation limit

**Source fact.** `Capture::intern` canonicalizes endpoints. `Capture::row`
(`candidate_scheme.rs:749`) resolves the intrusion representative, returns its
existing graph-row index on a capture-map hit, and otherwise stores
`Row { key: representative, local: level > boundary && !non_generic }`.
`CapturedRowObservation` is emitted only on this insertion branch. Thus a
captured observation records the first insertion's requested key and metadata;
it does **not** record every later capture-map lookup or its requested key.
`Capture::expand_row` (:1045) returns for a nonlocal row: its existing mutable
bounds remain session-owned, rather than being proved empty.

**Conditional inference.** Given an actual insertion observation, stored local
false follows from the recorded weak-level comparison or non_generic flag;
stored local true requires both strict level and genericity. A later alias
lookup cannot retroactively choose a new classification. Absence of an alias
lookup record cannot prove that no alias lookup occurred.

**Required observation per route.** Route and use, actual use occurrence,
capture root/boundary, graph-row index, requested key, representative, level,
non_generic and stored local. Distinguish recorded insertion from unretained
capture-map lookups. A claim about an unrecorded original requested key needs
separate source ancestry; equal representatives do not supply it.

## C2. Reconstruction map and separate route squares

**Source fact.** `prepare_candidate_fresh_use` (:1541) begins a distinct
context use and an empty per-use `canonical_rows`. At graph-row index i let
s_i be the representative read at that iteration, M_i the current map, and
g_i = stored_local_i && level_i > graph.boundary && !non_generic_i. The loop
at :1582 has the following exact successful branches:

```text
hit:  s_i in dom(M_i) -> image_i = M_i[s_i], no fresh allocation;
miss: s_i absent      -> image_i = fresh_row_at(use_level) if g_i else s_i;
                          insert s_i -> image_i into M_i.
rows[i] = image_i.
```

The test observation records graph_row, captured key, source_representative,
current level/non_generic, boundary, stored_local, canonical_rows_hit,
first_entry_graph_row, existing_image, allocated_fresh_image and image.
`allocated_fresh_image` requires a miss and true guard. A true guard on a hit
does not allocate. First-entry order follows the graph-row traversal, rather
than HashMap iteration order.

**Conditional derivation.** Induction over successful iterations establishes
that each hit reuses its actual earlier insertion. This uses the actual s_i
at each iteration and does not assume immutable representatives. If the
representative is fixed over several iterations, their first encountered row
controls that fiber's image. Distinct captured keys can converge under ordinary
intrusion; different stored flags alone do not prove separate images.

Keep these two chains separate until the observation binds their actual data:

```text
(Module route0,use1,occurrence0,G0,row i)
    -> current rep s0_i -> actual M0 hit/miss -> rows0[i] -> terms0[node]
(Module route1,use2,occurrence1,G1,row j)
    -> current rep s1_j -> actual M1 hit/miss -> rows1[j] -> terms1[node]
```

**Source fact.** `Node::Row` rebuilds the live term from its graph-indexed
mapped image with the original polarity; `Node::Function` reconstructs its
children in `[A,AE,RE,R]` order. Therefore each exact G/u square commutes by
the map assignment and term constructors. Equal indices in G0/G1 are not
identical source positions. Distinct use identities survive a shared image.
Fresh allocations are distinct at allocation; later representative equality
requires its own ordinary equality/intrusion evidence.

**Required observation.** Bind both complete route row arrays and all recorded
capture/reconstruction fields. Check each actual map hit against the indicated
first insertion and existing_image; compare canonical endpoints where needed.
Do not infer a missing first insertion from a final row number.

## C3. Producer, physical emission and ordered Function edges

**Source fact.** `candidate_bound_origin_with_evidence`
(`candidate_effect.rs:464`) constructs admission relations for their actual
OwnerEmission/FreshUse causes. `candidate_insert_bound_with_evidence`
(`candidate_extrusion.rs:499`) canonicalizes owner/item, admits the bound,
appends to its physical lane and retains admission-linked readback evidence.
`candidate_begin_bound_restoration` (:763) consumes that result.
`begin_candidate_fresh_bound` (`candidate_scheme.rs:1846`) rebuilds endpoints
from the exact use map, preserves orientation, constructs the FreshUse transport
and passes imported antecedent, use origin, source bound and mapped relation
to restoration. An OwnerEmission processing relation is not a use identifier.

**Source fact.** `candidate_context_begin_replay`
(`candidate_context.rs:3753`) meets actual lower/upper retained fibers, forms
the ordered task pair and retains the exact Replay recipe/dependency. It rejects
a lower demand, composes transformers and uses the upper demand. Source-support
union is not source-occurrence attribution. `authenticate_replay_ancestry`
(:2783) checks bound membership, ordered pairs, exact Replay and FreshUse
dependencies, demand/roots/flows and four distinct FunctionPort children. The
new observation must obtain these edges independently of authentication success.

Actual Function dispatch (`lib.rs:12652`) gives this endpoint falsifier for
lower positive L=(La,Lae,Lre,Lr) and upper negative U=(Ua,Uae,Ure,Ur):

| Field | Ordered lower endpoint | Ordered upper endpoint | Operation |
| --- | --- | --- | --- |
| A | Ua positive | La negative | Swap |
| AE | Uae positive | Lae negative | Swap |
| RE | Lre positive | Ure negative | Preserve |
| R | Lr positive | Ur negative | Preserve |

**Required observation.** Bind the actual lower producer occurrence/ancestry,
Relation58 pair, admission and physical emission/readback, lower/upper Function
roots and both port arrays, and all four concrete FunctionPort relation IDs,
pairs and ancestry. Numeric IDs name only the selected specimen, not an
independent semantic identity. A term match in route1 cannot establish route0
containment. Canonicalize row-valued endpoints before comparing polar pairs.

## C4. Consumer completion, NotReached and NotRetained

**Source fact.** `candidate_context_step_replay_child` (:3858) passes the
retained child relation and matching operation/index ack to `start_typed_drain`
(`lib.rs:12272`). Running checks the exact drain frame, ack, occurrence and cause.
`candidate_step_typed_drain_terminal` (:12728) prepares and retains the return
before popping that frame. The Ready branch checks queued/consumed counters and
drain-stack length, emits `ReplayDrainObservation::ChildReturn`, then returns
Delivered. `DriveReturn` records a driver outcome; Queued is not completion.

**Conditional classification rules, not an observed result:**

- Completed requires the actual child relation, operation/index ack, drain and
  terminal/return receipt to match. A different child's return is insufficient.
- NotReached requires a source-grounded control-flow derivation that this
  exact operation/child's start or return branch was never reached. The old
  test's post-authentication logger being unreachable proves only that logger
  was not reached; it does not prove inference never ran the drain.
- NotRetained means a required identity/receipt was not retained or exposed.
  It leaves execution/reachability unknown. An empty observation vector, a
  retired operation, or absent live drain cannot alone establish NotReached.

`test_replay_drain_observations` exposes the retained vector;
`test_emission_contents` exposes admission/bound/slot/readback. Their existence
does not guarantee coverage of a particular selected child. If the new test
cannot associate a receipt with that child, retain NotRetained and name the
missing association at these consumer owners. No extra instrumentation or
production edit is authorized to repair that gap in this proof lane.

## Runtime application — pending

**Observation: NONE supplied for the new exact test.** Instrumentation review,
exact invocation, source/executable hashes, stdout/stderr, exit status and fresh
reviewed correspondence are pending Luna intake. The test identity is
`candidate_scheme::authentic_demand_capture_tests::replay_constructor_lineage_observes_rejected_cross_route_authentication`.
No classification, passing-test claim or drain result is asserted here.

If both actual route squares select a shared anchored image and producer/ports
agree, that supports the row-sharing explanation for this specimen; a missing
drain receipt still limits the consumer conclusion. If a required fresh miss
or map/port incidence is demonstrably lost, report its owning constructor and
violated premise before requesting a correction. Otherwise state the first
unknown edge and owner. None of these outcomes alone proves universal receive
transport, original ?e_Op, F1/FK1, complete Call/effects, soundness, principality
or termination. The original complete dependent map, authentic ingress/future
coverage and actual residual consumer remain required.

## Reuse, dependencies and checks

Reuse the prior CLEAN ownership audit only for its actual observations/gaps
and C1–C4 draft only as conditional source guidance. The new source locators
and guards above were inspected at the r4 baseline. Reject same-route
containment, support union, family equality, final-row equality and assumed
transition tests as substitutes for constructor/occurrence correspondence.
The r2 rejected bytes are explicitly adopted instrumentation baseline, not
recovered pre-r2 provenance or production approval.

| Direct input | SHA-256 |
| --- | --- |
| r4 contract | `1eed76f1c8d9f9fb115a1f2a26a9845da230e7c17762cf3350d691190f43c049` |
| prior ownership note | `572884a8df2e8adc19eb1a8121277c77784e3c02fa9925729e292dd629f40308` |
| prior ownership handoff | `f2c93d65ba96e4a256010e2942096ca21ef714b5b06d81573701eb0b960948ed` |
| conditional C1–C4 draft | `36d9858b14f89c3636d7580fc78c3a217039314304f43a1a7da3cfb1e2e680f8` |
| scheme baseline snapshot / live source at intake | `b05bbf4d683df4d8c520ab215770dc33545225484c626ec82c17e06779db8cbc` |
| context snapshot / live source | `22a42a41253161f33d68f9670ee64868c684c99bc692380c018f76a013abe147` |
| lib.rs | `ddd1395877d4a76e27a1dcf32af90c6fcb0e58c739610a0115c03955628350e1` |
| candidate_effect.rs | `9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212` |
| candidate_extrusion.rs | `fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d` |
| inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| adoption receipt | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` |
| adopted NPAIR proposal | `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006` |
| native implementation contract | `36d9792d7a5bb4d06beeb4a1c62df28d38ff171fc324783061c2219a970ce064` |
| original construction frontier note | `2b526b92ef78b8514a81592b303e4db2310dedd13483c74bcfb4bd53798f0a8f` |

Checks so far: read-only source/authority inspection, baseline/input SHA-256
checks, exact output absence check; no runtime, tests, Git or source writes.
Only this note and its assigned proof inbox are new paths; no scratch paths.
No producer/coauthor certification. Fresh final review belongs to Luna.

Source-only stage cessation: 2026-10-18 03:01:30 UTC; observed timestamp
interval 92s, charged conservatively 100s of the 180s proof grant; at most
80s remains for reviewed-runtime binding. ACK-only startup preceded this
timestamp interval and was not measured. CPU/RAM telemetry UNKNOWN.
Draft writes stop on returning this stage; no frozen result is submitted.
