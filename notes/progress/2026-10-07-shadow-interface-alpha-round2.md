# Supplied finite interface alpha-isomorphism: shadow round 2

Date: 2026-10-07 (JST; UTC session date 2026-10-06)
Baseline: `ad514061de2792c374a4b5c224dff7f4772906e8`
Branch: `research/simple-sub-intrusion`
Status: independently reviewed shadow implementation; six focused tests and feature-off core check passed
Review and executed evidence: [round-2 integration record](2026-10-07-successor-round2-review.md)
Authority scope: current user-authorized default-off shadow implementation only

## Exact scope and theorem dependency

The implementation follows CI_ALPHA / CI-encoding in
[recursive synthesis §5.1](2026-10-07-successor-recursive-synthesis.md), whose
research theorem review is recorded in
[full-attack review](2026-10-07-successor-full-attack-review.md).
That independently reviewed mathematical statement is not an independent
review of this code. This note promotes no semantic or production gate.

`crates/yu-core/src/shadow_interface_alpha.rs` accepts an already supplied
finite typed incidence presentation. A node has an immutable sort and ordered
fields, each explicitly rigid or a local reference. Presentations retain
ordered designated exports and ordered rigid/external context. Generic Rust
sort and rigid-value types allow callers to provide their own typed records.
Callers remain responsible for representing the full binder tree/order/modes,
scopes, source occurrences/origins, direction, independent provider protection,
primitive identities, active kernels and all external observations. The module
cannot certify that these fields are complete or correctly classified.

The algorithm exhaustively enumerates sort-preserving bijections into slots
whose sort labels are sorted. Each complete ordered graph is compared using
Rust structural `Ord`; no string concatenation or unfolding of recursive edges
is used. The least whole graph and its original-to-canonical renaming are
published only after every candidate is examined. Equal completed forms yield
an actual original-left-to-original-right bijection and its explicit inverse.
A separate certificate verifier checks both inverse lengths/bijection and the
entire transformed graph, including immutable sorts, context and exports.

The certificate is only structural alpha-isomorphism of these supplied
records. It proves neither complete interface/source generation nor semantic
equivalence, primitive covariance/equivariance, Generalize eligibility,
source completeness, inference success, or production cutover. No existing
identity plumbing or production inference caller is changed by this lease.
The primary owns feature-gated registration in `lib.rs`.

## Research resource boundary and errors

The local-node envelope is eight nodes, at most 8! = 40,320 candidates when
all nodes have one sort. Each query additionally supplies a candidate budget;
comparison allocates that budget independently to each side. Node overflow or
a budget exhausted before a further candidate is explicit `Exhausted`, never
`StructurallyDifferent` and never a partial equality certificate. Zero budget
also exhausts the one empty-graph candidate. A budget exactly equal to the
candidate count completes successfully. All local references on both inputs
are validated before comparison returns a resource status; malformed node or
export references are distinct errors with their occurrence and target.

The mechanism is intentionally factorial research code, with recursion depth
bounded by eight. Graph-record size is caller supplied; the node/candidate
limits do not purport to bound total record bytes or generic `Ord` cost. This
is not a newly chosen production supported-input envelope.

## Verification ownership and frozen handoff

The exclusive lease consists of this note, the new module, and
`crates/yu-core/tests/shadow_interface_alpha.rs`. No manifests, shared task/maps,
questions, existing expectations, or Git state are modified by the producer.
The primary is the sole Cargo/build/test verification owner. **No Cargo,
build, test, or compiler process has been run by this producer; tests are
written but no passing result is claimed.**

The six focused test cases attack cyclic nontrivial renaming and inverse
certificates, every retained observable/order distinction, shared versus split
nodes, resource exhaustion including right-side exhaustion, malformed local
references, and the unique empty-graph candidate. Their actual verification
and any independent implementation findings must be recorded by the primary
before accepting this implementation gate.

Shared record synchronization in `tasks/current.md` and theory maps is deferred
to the primary; no implementation or theorem closure is asserted here.
