# Module-use retained native transport

Date: 2026-10-17  
Status: corrected candidate source-byte proof; independent review pending
Sprint: `module-use-retained-native-transport-20261017`, revision 2
Author: `/root/module_freshuse_retention_proof` (prover; sole author)

## 1. Claim and exact parent application

Fix any successful candidate module incoming-route transaction in the frozen
implementation below. Let G be the exact owned Graph passed to
`instantiate_candidate_graph`, and F the FreshUse returned by its retained
freshening call. The committed FreshRoute owns G, F.rows, and every non-row
field of F, without reconstructing, cloning or filtering the crosswalk. This
ownership lasts until that route is removed or its GraphState owner is dropped.
Successful inference finalization can transfer GraphState to the frozen result;
it does not necessarily drop GraphState when the session is consumed.

The compiler capacity charge for this transfer is exact in the capacity model
defined in section 3. Failed transactions remove newly published route entries
through the existing rollback boundary; earlier failures publish none. No claim
of exact physical allocator usage, immutable native referents, complete failure
capacity restoration or reusable IDs follows.

This establishes only the durable module-remap prerequisite in the native
field-map readiness contract sections 2 and 5. That contract's historical
statement that module non-row maps expire is replaced, for these frozen
candidate bytes, by the ownership fact above. All source field producers,
source Sig, actual handle class, semantic eligibility, total Phi_u, root/Call,
F1/FK1, N-Transport, soundness, principality and termination remain open.
Original theorem conditions closed: **0**. No original quantifier, admitted
source domain or requirement is changed.

## 2. Actual construction and ownership proof

The relevant source is `candidate_scheme.rs`: FreshRoute at lines 119–124,
FreshUse and its split at 192–216, retained freshening at 1132–1168,
module instantiation at 1495–1545, and owner recount at 323–344.

`freshen_candidate_graph_core` calls `prepare_candidate_fresh_use` once, then
restores every captured bound in Graph order with that same F. It obtains the
root from F.terms[G.root] and returns `(root,F)` only after successful restoration.
Thus F is the actual output used by native restoration, rather than a later
crosswalk guessed from equal-looking endpoints. Existing row eligibility,
canonicalization, scope copying, bound orientation, evidence import, bundle
and context transport are reused unchanged. This lemma does not prove their
source semantic adequacy.

The retained wrapper returns that F, after accounting its completed transition
storage. Module instantiation immediately calls `F.into_retained_parts()`.
Destructuring moves all nine FreshUse fields: rows separately, and scope_remap,
scoped_relations, context_use, terms, effect_operands, bundle_remap,
context_remap, evidence_remap into RetainedFreshUseMaps. ScopeRemap itself owns
its regions, scopes and inputs maps. There is no residual field to drop, map
restriction, fresh iteration, remapping or clone in this split. Consequently
all keys, values, vector order, absent entries and capacities are preserved.

Instantiation reserves route storage, computes checked charges, samples,
and calls the existing `route`. Only after route success does it push
`FreshRoute { use_id: id.clone(), graph: G, rows, retained }`. These owned
values are moved into one route with the actual module use ID. Capacity was
reserved before the push and no intervening operation appends to this routes
vector; `route` records the ordinary incoming route rather than recursively
instantiating a module Graph. The final resource sample remains fallible and
therefore the push is tentative until the enclosing transaction succeeds.

GraphState owns `Vec<FreshRoute>`. Appending/moving a Vec or GraphState can
relocate headers but does not clone or discard their owned payloads. No raw
address or externally escaping reference is introduced. Later direct lookup
in the stored crosswalk therefore reads the actual retained map. Equality of
later dereferenced native object fields needs its own live-owner/version
premise: retained ContextId, RowKey or EvidenceSnapshotId is not an immutable
snapshot of the object it identifies. This proof supplies no historical read
API and no authentication of IDs after rollback reuse.

Compatibility entry point: `freshen_candidate_graph` keeps
`Result<(Term,Vec<RowKey>),SolveAvailabilityError>`, calls the shared core,
projects rows, explicitly drops non-row maps and restores entry scratch on
success/error. Only the module retained helper changes the ownership policy.
It does not impose retained-map semantics on other callers.

## 3. Exact checked capacity identity

Write B(T,c) = checked `c * size_of::<T>()`. All sums below use checked
addition. Let R be B(RowKey, F.rows.capacity()). Let M be:

```text
ScopeRemap.bytes()
+ B((RelationId,ScopedFlow), scoped_relations.capacity())
+ B(Option<Term>, terms.capacity())
+ B((usize,EffectEndpointKey), effect_operands.capacity())
+ B((AttachmentBundleId,AttachmentBundleId), bundle_remap.capacity())
+ B((ContextId,ContextId), context_remap.capacity())
+ B(EvidenceSnapshotId, evidence_remap.capacity()).
```

ScopeRemap.bytes counts all three of its map capacities. FreshUse.bytes is
exactly R+M by inspection; RetainedFreshUseMaps.bytes is exactly M. Moving the
fields preserves each capacity, proving the split identity without allocation.
The six outer backing vectors/maps and three nested scope maps have exactly
one payload owner each. context_use is an inline scalar. The route headers,
Graph headers, vector/hash headers and inline scalar are covered by
`B(FreshRoute, state.routes.capacity())`; payloads are counted separately.
Referenced session-native contexts, relation/evidence objects, scopes and
term payloads remain owned/accounted by their original owners; an ID-map entry
does not duplicate those native payloads. Graph.bytes separately enumerates
its ten backing collections. The identity uses their existing compiler model.

Let S be caller scratch before graph capture, G = Graph.bytes() for the
captured graph, and F = R+M for the actual returned FreshUse. Capture adds G to
scratch before calling the retained helper, so that helper's entry charge is
E = S+G. On successful return the helper normalizes scratch to E+F,
eliminating expired constructor temporaries from this completed transition
charge. Let P be the prior retained charge, C0 and C1 the route capacities
before/after successful reservation, and D = B(FreshRoute,C1-C0). Instantiation
transfers both the already-captured graph and the completed FreshUse payload
out of scratch. The checked move computes exactly:

```text
retained' = P + D + G + F
scratch'  = (E + F) - (G + F) = S.
```

The charge subtraction is checked; multiplication, addition, Graph and map
charges are checked; reservation is fallible. Since E=S+G and F=R+M, the
transfer leaves the caller's original scratch S while adding each transferred
capacity to retained ownership exactly once. The focused regression asserts
`scratch_bytes == entry_scratch` immediately before the prepublication resource
sample, after the transfer and before the tentative route is pushed. No
wraparound is accepted.
Before push the retained counter deliberately precharges the private pending
route for resource sampling; it is not at that instant an enumeration of only
published route entries. On successful push and transaction completion the
charge matches actual new retained owner capacities. On error rollback
recounts instead of trusting an incomplete incremental charge. Incoming
caller scratch is restored by `route_candidate_graph` on either result.

The full `refresh_bytes` sum counts route Vec capacity once and each live
module route's G.bytes, R and M once, together with separately enumerated
stored graphs, local routes and local continuation frames. Hence, assuming
the prior owner sum was correct, each successful module-route extension
preserves that sum; initialization establishes it by refresh_bytes. The
focused test supplied by Luna confirms an authentic module execution agrees
with the recount. That test is corroboration for this algebra, not coverage
of all constructor field populations or failed transactions.

These are compiler capacity units. HashMap allocator bucket/control bytes,
allocation metadata, stack storage and physical allocator fragmentation are
not measured. Existing separately charged orchestration/scratch/native
storage is not included in M. No exact physical peak or end-to-end asymptotic
solver bound is asserted. Additional persistent backing charge per route is
M, plus the retained-record inline increase over route vector capacity;
rows and Graph already persist. Splitting and computing M use a fixed
number of header operations, with checked capacity arithmetic; construction,
reservation/reallocation and solving retain their separate costs. Across
committed routes, additional backing charge is the sum of their M values.
Rollback drops the removed map entries; work follows actual collection drop
and allocator behavior, with no benchmark or constant-time claim.

## 4. Rollback, drop and failure boundary

`lib.rs:16652` route_incoming wraps route_incoming_inner in
with_route_transaction; its candidate arm calls route_candidate_graph.
The journal records candidate_routes_len before mutation (`lib.rs:9205`).
`finish_route_transaction_with_candidate_accounting` commits on Ok and
invokes rollback_route_transaction on Err (`lib.rs:9281–9326`).

Before the route push, an error from construction, restoration, reservation,
checked arithmetic, sampling or `route` drops the local G/rows/maps when
its owning stack values unwind. No FreshRoute from that attempt is published.
After push, a failing final sample is returned through the same transaction.
Rollback restores the intrusion checkpoint and truncates routes to the saved
length (`lib.rs:9478`). Rust Vec truncation drops each removed FreshRoute,
therefore its Graph, rows and all retained maps. It leaves vector capacity
allocated. refresh_bytes then charges the surviving route capacity and only
surviving route payloads, and scratch is zeroed. Successful rollback does not
promise prior physical capacities, all scope inventory reclamation or
monotonic/reusable record IDs. If rollback itself cannot complete, the
availability error propagates; this proof does not authorize continued use
of an inconsistent private attempt or a successful partial result.

Transactions whose saved length already includes a route preserve its
prefix entry. No arbitrary outer rollback immunity is inferred. When a
session is dropped without transferring GraphState, owned fields recursively
drop it. On successful finalization, `finish_observations` moves
self.candidate_graph into FrozenInferenceData (`lib.rs:17755`), and
finish_candidate retains that data in CandidateSolvedResult. Those routes
therefore survive session consumption until the final result/GraphState
owner is dropped. There is no intentional leak, external map ownership or
manual lifetime extension introduced by this change.

## 5. Reuse, evidence, remaining task

Reused: the private local-route retained record and move construction, and
local-map retention's distinction between direct stored-map answers and
version-dependent native dereferences. The earlier local theorem's historical
code statement about dropped non-row maps is not current-code authority.
Rejected implications: local source semantics for module handles, row identity
as source binder ownership, evidence snapshots as EventProof, source handle
class inferred from native routing, and any total source/native map conclusion.
No withdrawn Simple-sub bypass, altered generation, reduced propagation,
weakened generalization or collapsed lineage is used.

Luna supplied (not run by this author): repaired-source cargo check PASS;
focused `module_fresh_route_retains_full_remap_crosswalk_and_capacity_accounting`
PASS 1/1; diff whitespace check PASS. The initial signature failure was repaired
before these frozen checks. This author performed read-only source/authority
inspection and SHA-256 validation, with no tests/builds, code edits or Git.

Next single semantic condition remains HINTRO-OWNER-u_id: the authentic owner
must derive the exact occurrence handle from the original source rule and
publication environment. Separately MODULE-NATIVE-FIELD-MAP requires source
Sig/field incidence, allocation classes and witnesses before these retained
native images can be applied to a whole source tuple. Falsifier for this native
lemma: a FreshUse field is discarded or rebuilt at the split, the charged
capacity differs across the move, a committed route is missing its map owner,
or a failed transaction leaves its appended route visible. No such case was
found in the frozen control flow; independent review remains required.

## 6. Frozen source/dependency pins and cessation

```text
contract rev2 b193043d56e60af7bfea4f8de7310a1230ae39546df70455bc4fa4b788184604 (rev1 1cdbd0706203b0d34c13aa0f7e7342e3413dbc3fbd90b40e335b294bdbe820c2 superseded)
candidate_scheme.rs abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494
implementation handoff rev3 7537cd9744d77ca2d100b7996237daaa858123ae0f84c2ded35d00eacfd12a28
candidate_source.rs efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38
lib.rs 2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f
native field-map contract rev2 1465b65979b2742de020c2bc7b44ff6fb53adefa7158d9fa3947d0b4d5923502
handle introduction df0e684bad2da05741e39db12bd06bb400ad8b5b15af4116abab4df6c9df06c3
local-map retention f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e
```

All contract input pins and the implementation revision3 source/handoff pins matched at correction.
Candidate-context type declarations were inspected only to check that the
counted value records contain inline IDs/values, not separately owned hidden
payload collections; observed SHA-256
`72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`.
Revision 2 corrects the transfer equation after compiler review found that
Graph bytes were already present in helper-entry scratch. It uses E=S+G and
transfers G+F, and records Luna's focused prepublication assertion and
targeted test receipt. Luna owns this bounded correction. The initial proof
author remains STOPPED. No source, theorem scope or semantic rule changed;
independent review of these corrected pins remains required.
