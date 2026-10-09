# Successor mixed value/effect graph schemes

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Code baseline: `90629b21682e3aecb51df7de4f7cdd801212647a`
Scope: nonshipping top-level graph generalization and actual incoming-use routing
Authority: current Simple-sub correction and existing source/constraint contracts;
no new semantic adoption or production publication authority
Mode: M2; compiler-referee and performance-auditor; measurement budget zero

## Operational implementation

`shadow_apply::CandidateInference::solve` selects the private graph scheme path
inside the existing `InferenceSession`. This is connected to actual dependency-
first SCC publication and incoming DefinitionUse routing, rather than an unused
snapshot or separate model solver. Ordinary F5 and `CandidateValueObservation`
retain their prior paths. The graph path does not require F5's pure closed-scheme
exporter, and its result cannot be published as an ordinary `SolvedModule`.

The new `candidate_scheme.rs` retains indexed structural nodes, kind-qualified
value/effect rows, all four Function ports, direct row edges and exact structural
bounds. Graph ownership is flat; cycles pass through row identities. Each use
allocates its local row substitutions before reconstructing structural nodes,
with one mapping shared throughout that use. Anchors reuse existing live rows.
Replayed bounds and the root constraint enter the existing typed solver through
the actual use occurrence/cause and existing incoming-route transaction.

The admitted boundary is the existing top-level boundary zero. Actual levels
and `non_generic` metadata determine row eligibility. Captured outer formals
remain in the containing definition's graph; this adds no separately generalized
nested initializer. Source-internal SCC uses remain excluded by candidate
admission. Anchor structural dependencies are checked across all four ports;
general environment/non-generic closure, including direct anchor adjacency, is
not established by this slice. Current admitted startup/fresh rows are level one
and not non-generic, so review found no admitted-source failure of that boundary.

Borrowed exports and fresh-use observations retain their graph/result owner.
`candidate_conflicts()` exposes the existing recovered solver diagnostics
without copying or reconstructing their occurrence/cause. An `Ok` candidate
solve alone is not evidence of conflict-free inference or certified source
acceptance.

## Independent review and adjudication

The compiler referee inspected the frozen graph, live constraint/SCC/route
dependencies and artifact identities. One major finding was accepted: the new
observer lacked the legacy observer's conflict accessor, hiding recovered
`IncompatibleValue` errors. A separate implementer added the borrowed accessor.
The fresh compiler-referee delta review closed the finding by tracing the
accessor to the owning diagnostic slice and retained occurrence/cause. No
accepted BLOCKING or major finding remains in that semantic review. Its closure
is restricted to the accessor and diagnostic ownership; no runtime invalid-Apply
witness is claimed.

The resource auditor found expected linear capture and structural reconstruction
per graph, iterative structural ownership, no whole-arena scan or graph clone,
and journalled fresh-row/route cleanup. Costs include solver propagation beyond
that linear reconstruction: every retained bound enters the existing worklist.
Direct edges can be retained from both adjacency directions; pair memoization
handles repeated logical edges. There is no overall linear-time inference or
performance-improvement claim.

The auditor classified missing failed-capture footprint samples as major. The
primary retained this as an explicit evidence limitation rather than requiring
new allocation-event instrumentation: no complete failure-peak claim, numeric
resource limit, RSS claim or retry-after-unavailable guarantee was selected.
Successful checkpoint samples account logical capacities. Allocation/endpoint/
anchor rejection before the final capture sample does not establish that
attempt's high-water footprint; failed candidate solves return no result.
This disposition does not claim comprehensive failure accounting certification.

Each definition retains its own reachable graph; each use retains its row map
and additional live solver state. Storage scales with the sum of captured
definition graphs and use row maps, not just one global graph size. The observer's
`fresh_use` lookup is linear in retained use count; observing every use by repeated
lookup can be quadratic. No lookup index or measurement campaign was added.

## Checks and frozen evidence

Primary checks:

```text
RUSTC_WRAPPER= cargo check -p yu-solver --features shadow-apply-candidate -j 2 --offline
RUSTC_WRAPPER= cargo check -p yu-solver -j 2 --offline
git diff --check
```

Both owning builds passed without warnings. The candidate build was repeated
after the accessor repair and passed. No tests, execution probes, benchmarks or
workspace-wide suite ran. Measurement consumption: zero processes and samples.

Final code SHA-256 before integrating the separate remote test registration:

- `lib.rs`: `8e6c7330c9d702dab30a9554413b30bdd213a3a95f1033c57c3017a3724d45bf`
- `candidate_scheme.rs`: `4e3849e9b1b4c8ec4edcf76894c293f1fc6833bb10caa1134019a04cdd3b67d8`
- `shadow_apply.rs`: `68bd38df041011efca38db2ea63b423c743c6e3e14ae0a24df8cd1242ce21778`

## Next owner and remaining scope

The first checkpoint retains the current pure source recipes. Next select graph
collection before constructing the batch, retain actual child effect components
for Apply/Group, allocate an invocation effect row, put argument evaluation in
the negative Function demand, and route callee evaluation/invocation output into
application evaluation. Group forwards its child's effect. Preserve unannotated
Lambda construction/parameter ownership and legacy candidate behavior.

Runtime scheme/fresh-use behavior, structured effects, receiver/protection
elaboration, complete Call provider/world/image/admission/license/future fields,
polarity-copy extrusion and ordinary public scheme extraction remain open.
Existing extrusion still lowers live levels in place; it is not certified as
Simple-sub's polarity-keyed copied approximation. No proof-DAG node or complete
Call/publication gate is closed. The requested F5 replacement on `yulang3` has
not occurred and the full objective remains active.
