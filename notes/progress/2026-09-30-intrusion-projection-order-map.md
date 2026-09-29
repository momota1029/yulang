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

No compiler code or tests changed or ran. No Python or measurements were
used.
