# SCC intrusion Oracle projection-order map

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: read-only source map; no projection-congruence theorem

## Selection path

The scheme collector creates a projection round and retains the first query
failure. Positive visits query scoped projectable lower records and merge
selected bounds in returned order. For each variable, lower enumeration is
evidence records first, then ordinary records; promotion appends a record to
the ordinary vector. Each record may be `Excluded`, `Unclaimed`, or `Included`
with a qualified support set and projection evidence. Negative visits read a
separately ordered upper projection.

Relevant frozen source locations:

- `compact/collect/mod.rs:80, 833, 848, 898` — per-root projection round,
  query failure, positive lower collection and merge order.
- `constraints/mod.rs:2529, 2631, 2664` — evidence/ordinary lower storage,
  promotion, and enumeration order.
- `constraints/structural_kernel/access.rs:862` — decisions for every lower
  record in enumeration order.
- `constraints/proof/mod.rs:9975, 10059, 10113` — target checks, support
  inclusion, and cycle-cut behavior.
- `constraints/proof/mod.rs:10565, 10615, 10669, 10801, 10873` — formula
  revisions, sorted supports, support-to-incidence checks, representative
  claim/coverage-root binding, and premise validation.
- `constraints/proof/mod.rs:11704, 11735, 11918` — ordered formula
  evaluation, first decisive included arm, and cycle handling.
- `constraints/proof/mod.rs:5021, 5107` — structural snapshot mutation
  identity, distinct from constraint epoch and evaluation round.
- `constraints/structural_kernel/access.rs:318, 360` and
  `constraints/proof/mod.rs:191` — query scope authentication and failure
  latches.
- `compact/surface.rs:12, 174` — returned query error can become a default
  compact root at the surface.

## Congruence requirement

An `R_i` proof-carrier relation needs more than a mapping of variable and edge
identities. The proof store separately tracks support ledgers, formula
buckets/incidence, upper claims, coverage roots, live row states, and premise
dependencies. Representative claims and coverage roots must stay distinct.
Formula certificates are revision-sensitive; structural snapshot identity is
not the same clock as solver epochs or evaluation rounds. These dependencies
and invalidation conditions must correspond, rather than requiring equal
numeric epochs.

A concrete obstacle to simple injective-renaming equivariance is that
canonical formula ordering compares numeric coverage-root, carrier, record,
constraint, and premise IDs. `project_lower` stops at the first included
canonical arm and records it as decisive evidence. Reallocating proof IDs can
therefore change visit order, error precedence, or the decisive witness even
if the selected inequality graph is isomorphic. A proof must either transport
the relevant order and support incidence or show that a changed witness is
unobservable through all downstream selection and reporting. Projection-round
cycle-cut and memo state also affect later record evaluation.

The current `R_i` draft now records these requirements. This source map does
not show that a suitable transport exists, that witness changes are harmless,
or that Oracle and intrusion choose the same lower edges. That remains the
next projection-congruence obligation before whole root-step simulation.

An independent spec-auditor delta review confirmed the cited selection/order
facts and found no blocking or major issue in the amended `R_i` condition. The
review inspected collector order, per-record decisions, the first decisive
included arm, and promotion to ordinary storage; it did not audit every proof
path or runtime trace. The relation deliberately treats order transport and
downstream witness unobservability as open proof obligations.

## Downstream decisive-witness route

A read-only follow-up traced `ProjectionEvidence::DecisiveClaimedArm` through
generalized witness capture. Compaction itself discards the reason/evidence
payload and merges the same included bound. Witness capture separately stores
only the decisive claimed certificate as an exact lineage parent. The
generalized witness then feeds explanation traversal and an exported portable
provenance sidecar, which can preserve the selected producer/source site.
`BuildPolyOutput` exposes `subtype_provenance` publicly; the sidecar contains a
snapshot, occurrence table, and metrics.
Thus, if two exact included arms have distinct source lineages, a numeric-order
change may leave the compact type constraints unchanged while changing
observable provenance. The candidate relation must map that lineage to the
same normalized public cause or prove the observation contract intentionally
forgets the difference.

The inspected ordinary use-instantiation path consumes a generalized witness
ID, path, and completeness; it does not clone incoming parent edges. For the
narrow case of swapping between two exact claimed arms with the same
qualification category, no change to inserted subtype constraints or later
projection was found. This does not cover `FailOpenIncomplete`, distinct
completeness, other import adapters, or every later provenance consumer.
Evidence: frozen `generalize/provenance.rs:218–270`,
`constraints/mod.rs:2960–3005`, `constraints/explain.rs:1426–1475`,
`analysis/session/occurrence_provenance.rs:230–280`,
`analysis/session/instantiate.rs:211, 394, 473`,
`lowering/body/mod.rs:133, 1659`, `yulang/src/source/mod.rs:1874–1885`,
`poly/src/provenance.rs:151–171`, and `proof/mod.rs:11704–11718`.

A regression-auditor delta review found that the draft's later `Observe_X`
paragraph still excluded auxiliary fields, contradicting the newly traced
public sidecar. The paragraph now includes every entrypoint-exposed auxiliary
field and sidecar, including subtype provenance, while leaving identity/order
normalization and a complete per-entrypoint public-field audit open. No other
repair was requested in that delta scope.

## Root mutation and query-round lifecycle

A read-only source pass traced the proof state across one Oracle root attempt.
Each generalization-loop iteration rebuilds the compact root and its scoped
projection traversal; a newly applied merge, subtype, cast, or role constraint
routes events and restarts the loop. The compact cache is keyed by root and
constraint epoch. Alias expansion and stack cleanup then each have one bounded
post-loop companion constraint pass. Either can mutate and route events, but
neither restarts generalization, so a saved view may describe the compact
snapshot from before those final mutations. A root-step relation must retain
that saved view as an observation and relate the successor solver state
separately.

Within one compact attempt, the collector owns a fresh
`ProjectionEvaluationRound`; restarting creates another. The query's evaluator,
memo, and cycle-cut state therefore need to correspond within each attempt,
not be transported across restarts. The active P0 scoped gateway's round reuse
slot remains `SealingIncomplete`; the persistent `Sealed` form is dormant, so
the proof must not assume persistent cross-call reuse. Separately, formula
buckets have per-record structural revisions and certificates that validate
formula order/membership/support structure. The global proof structural
snapshot counter is bumped by many proof/constraint mutations and saturates to
permanently nonreusable, but the inspected P0 production read path does not
currently use that counter as a cache key or invalidation gate. These are
distinct clocks and mechanisms.

IDs are not all fresh opaque names: bound records reuse canonical keys or
append, constraint records append from record-vector length on admission,
formula/support entries append in accepted event order or reuse exact keys, and
upper claims append. Bound records and constraint records therefore have
different reuse rules, and admission/allocation order does not determine
canonical formula order. Formula selection sorts by category, support,
carrier/premise, and lineage, with entry ID as an equal-clause tie breaker;
pending runs are merged by canonical key. A transition proof must preserve
the resulting cursor order and exact decisive lineage, not merely extend a
bijection on IDs. Source inspection does not establish that Oracle restarts,
post-loop mutations, and an intrusion implementation generate corresponding
mutation batches or preserve these orders. This remains an open root-step
obligation.

Evidence in frozen source: `analysis/session/generalize.rs:51–190, 465–535,
582–609`; `compact/surface.rs:14–25`; `compact/collect/mod.rs:80–91,
350–369, 850–867`; `constraints/structural_kernel/access.rs:125–132,
318–392, 343–348`; `constraints/structural_kernel/access/sealing.rs:3–31`;
`constraints/machine/entry.rs:1201, 1392, 1490, 1671`;
`constraints/proof/mod.rs:206–223, 3205–3230, 3678–3779, 5021–5145,
7226–7268, 7339–7391, 8064–8115, 8185–8330, 8330–8353, 8485–8509,
8550–8615, 8990–9028, 9975–10025, 10036–10125, 10555–10610`;
`constraints/mod.rs:2548–2582`.

No compiler code or tests changed or ran. No Python or measurements were
used.
