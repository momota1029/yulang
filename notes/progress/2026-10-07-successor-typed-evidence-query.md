# Finite typed Path and current incidence: shadow construction

Date: 2026-10-07
Status: implemented, focused tests passed; repaired compiler-referee and spec-auditor reviews passed
Authority: current user's settled default-off shadow implementation authorization
Semantic input: reviewed [typed-boundary realization §6](../design/2026-10-02-typed-boundary-realization-draft.md)
Production authority: none; no production caller or inference cutover

## Exact responsibility

`yu_core::shadow_typed_evidence::AssumedTypedEvidence` computes the finite
`Path` and `Inc_C` consequences of an independently supplied typed evidence
graph. It implements a settled query responsibility; it does not construct an
original profile, source licensing, `OriginalAssocType_X`, admission, typed
correspondence or source ownership. The existing pending call premises remain
pending. There is no source-to-semantic adapter hidden in the query.

The graph has canonical typed ports, supplied profile origins, directed typed
`Flow` edges, actual event `Observe` records and normalized `Receive` records.
A normalized receipt includes an independently supplied expansion of the
original corresponding-path evidence to the exact executing view/effect port.
It is not a raw receipt or proof that using a value as callee receives that
callee's public view. The candidate handler, its owner, original boundary
receiver and current activity sets are likewise independently supplied.

All records retain one borrowed original context packet, including its
`beta`, source scope, `xi=(nu,K,D)` and shared variable witness. The query
never compares their solved values, changes them or uses successful Q. Each
profile retains its own original witness and boundary even when other
profiles have equal endpoint values. No original contribution or inherited
provider arm is manufactured or merged.

## Identity contract and repaired findings

Caller-owned nonzero-sized tokens in stable, nonoverlapping borrowed storage
represent the **assumed canonical identities**. Their payload values do not
participate in equality. These are semantic evidence tokens supplied by the
caller, not addresses of runtime values, source positions, endpoints or
freshly packaged wrappers. Supplying a token asserts its identity; the helper
does not prove its source provenance.

The first submitted implementation compared `AssumedEvent` wrapper addresses,
although `AssumedEvent.witness` names the actual request. Both independent
compiler-referee and spec-auditor found that repackaging the same witness
would erase its Path. The repair compares the retained event-witness token,
with the same original-context checks. A same-witness wrapper now must retain
the result; a distinct equal-valued event token must not join. The spec
auditor reviewed this test-contract correction before it was written.

Both reviewers also found that `W=()` can give distinct purported tokens the
same address. Construction now returns `ZeroSizedWitness` before any graph
can be queried. This is a representation validity restriction on the
conditional helper, not source rejection or a language resource policy.

The original context wrapper is consistently the one canonical assumption
packet, as in the existing directional shadow adapter. A separately
constructed packet with equal fields is rejected rather than silently
combining independently supplied assumptions.

## Finite-query correctness proof

Let `G=(N,E)` be the validated supplied finite typed-flow graph. Nodes encode
the exact `(view,position)` witness identities, without duplicates. Let `s`
be the selected original profile node, `q` the canonical supplied event and
`u` the candidate's original owner. Define the target set

```text
T(q,u) = { n | Observe(q,n) and NormalizedReceive(u,n) }.
```

Both conjuncts refer to the same node, hence the same exact executing typed
view/effect position. Event equality uses the canonical event witness and
the original context. Normalization of the corresponding-path premise is
part of the input contract, not an inference from a node index.

The query returns `path=true` iff a directed path of length zero or more in
`E` goes from `s` to a node of `T(q,u)`.

**Soundness.** Initially only `s` is visited, witnessed by the length-zero
path. Every later node enters the queue only along a supplied edge from an
already reached node. Induction on enqueue order therefore gives a typed
flow chain from the same original profile to each visited node. A successful
endpoint test additionally supplies the matching `Observe` and normalized
`Receive`. These are precisely the supplied §6 `Path` premises. No other
profile, alias, event or receiver is substituted.

**Completeness.** Suppose a supplied path from `s` reaches a matching target.
Induct on its finite length. The starting node is enqueued. When a reachable
prefix node is processed, its successor is either already enqueued or is
enqueued by that edge. If the algorithm stopped earlier, it already found a
matching target and returned true. Otherwise all reachable successors are
eventually processed, including the target. Exhausting the queue without a
target therefore implies absence of any supplied Path witness. This is a
closed finite-graph statement; it does not assert source completeness of the
supplied graph.

**Current incidence.** The final conjunction tests activity of exactly the
candidate handler, its owner and the selected profile's original receiver.
By the independently supplied current activity sets, the Boolean is exactly

```text
Path(q,owner(h),b,p)
and Active(h,C) and Active(owner(h),C) and Active(b.receiver,C).
```

The observer need not remain active: its historical event witness persists.
Expiry removes current incidence while raw Path remains. A new equal-valued
receiver or an object reachable from a raw continuation cannot replace the
original receiver. Grant/release, operation coverage, handler ordering and
selection are deliberately outside this query's responsibility.

**Total finite traversal.** Construction validates every external node index
before adjacency indexing and rejects mixed context records or duplicate
canonical ports. Querying an invalid profile is a structured error. The queue
marks on insertion, so it contains at most `N` nodes and every edge is visited
at most once. Cycles require no unfolding. Mathematical termination is for a
finite supplied graph and successful allocation; no production allocation or
practical limit policy is implied.

Construction costs `O(N²+F+P+O+R)` time for the explicit canonical-port
duplicate test and record validation. Retained allocated adjacency is
`O(N+F)`. A query costs `O(N+F+O*R+A)` time and `O(N)` temporary space, where
`A` counts the queried active roots. These deliberately visible costs are
adequate for the opt-in research helper; no hot-path optimization is claimed.

## Tests, scope and integration

The independent reference calculation is Floyd–Warshall transitive closure,
compared with queue reachability on all 512 directed three-node graphs and
all nine source/target pairs: 4,608 path/incidence comparisons, including
self edges and cycles. Additional cases cover event repackaging, distinct
equal-valued tokens, wrong/missing Observe/Receive/owner/port, original receiver
expiry and raw re-entry, handler/owner expiry, malformed indices, mixed
contexts, duplicate ports and zero-sized token rejection.

A separate source-plumbing integration test parses the approved `apply/step`
source, retains its outer formal declaration and seven pending semantic
premises, applies the existing explicitly assumed directional adapter, and
uses that adapter's returned context/upper/output witnesses in the supplied
typed graph. An independent provider-owned profile remains queryable when
the original upper receiver expires. Without a supplied cross-view Flow the
upper profile cannot reach the separate provider event. This checks wiring
and supplied-relation consequences, not source generation of that Flow or
a new proof of source-wide no-backflow. No generalized interface/fresh scheme
is fabricated beyond the implemented chain.

Rust 1.90.0 focused checks passed: the three finite-query/identity tests, the
new source/conditional-incidence integration test, the existing directional
adapter test and all eight raw structural inventory tests. The old Rust
1.85.1 bootstrap failed on preexisting repository let chains before checking
this module; the compatible official toolchain resolved that environment
failure without a repository workaround.

This exhaustive **finite query** test is not a source-validity or all-world
model. It supplies all graph/typing/activity facts. It cannot discharge
source profiles, actual source evidence generation, recursive membership,
Generalize, all-view principality or production conformance.

The module is exported only under existing default-off `shadow`. It has no
production users, changes no existing source judgments, test expectations,
manifests or production inference routing. Removing the new module/export
removes the whole experiment. Final commands/results and independent repaired
snapshot review are recorded in the [full-attack review](2026-10-07-successor-full-attack-review.md).
