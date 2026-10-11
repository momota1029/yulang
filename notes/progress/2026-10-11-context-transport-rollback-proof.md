# Context transport: constructor and rollback seam

Date: 2026-10-11
Status: independently reviewed constructive local inverse derivation; requested accounting conclusion OPEN. No global W/A3 closure or production authority.
Producer: leaf `/root/retained_w_a3_rollback_proof`, no delegation.
Exclusive lease: this note only.
Baseline: `6c130940e077853672954640325b034b287a1e96`, branch `research/simple-sub-intrusion`; compiler inputs match the primary's `d7e87c637` repair baseline.

## Objective and frozen claim

Derive the operational cases of `InferenceSession::candidate_context_transport_task` and their actual rollback correspondence. Governing authority is [private candidate suspension](../design/2026-10-11-private-candidate-suspension-contract.md) §6: route failure restores the checkpoint, dependency admission is reserved before publication, and retained/rollback storage is accounted. This note does not reinterpret §6 or approve a different accounting rule.

Fix a constructor-valid session with `shadow-apply-candidate`, an active route journal C, valid task t, and optional valid relation r. If r is present, its stored raw endpoints canonicalize to the task's pair, and its context/residual IDs are valid. Collections and their index/head/log invariants are constructor-owned. Let B be the state immediately before this call. All input identities remain distinct; canonicalization changes execution endpoints, not retained occurrence, context, attachment, provider or residual identity. The finite Q/A/H and all original source binders of [W/A3](2026-10-11-nonterminal-drain-owner-composition-proof.md) are unchanged; this local packet supplies no scheduler or source-reachability theorem.

**Requested conclusion:** the call either has no state change for None/equal raw pair, finishes relation plus Derived dependency admission and its resource sample, or returns an error; on an error after partial construction, owning session rollback restores exact pre-call relation/dependency/context counts, lifecycle generation, processing context and accounting census.

**Actual claim class:** constructive case split and exact local logical inverse, with explicit transaction-prefix conditions below; the full requested conclusion remains OPEN at the accounting owner. This is a derivation from actual emitted logs, not a checker supplied with hypothetical transitions. No tests, allocator experiment or constructor-qualified counterexample was produced.

### Transaction-prefix conditions and runtime assumptions

Route rollback targets C, not a checkpoint newly created at B. For an exact **pre-call** conclusion, the prefix C→B must preserve the named logical projection: relation/dependency/context counts, lifecycle generation and the processing value. For the isolated local inverse proof below, context undo/frontier ranges unrelated to this constructor are empty at B relative to C. Existing context state, relations, dependencies, bundles, edges and transport indexes at C may be arbitrary constructor-valid finite objects. Their objects need not be fresh or empty.

These conditions are sufficient hypotheses of the local composition, not new restrictions on the original W/A3 domain. If a real route prefix already changed the projection, the owner will restore C's value, which need not equal B's value. Establishing the appropriate actual prefix correspondence is therefore required before using the pre-call wording. In particular, actual typed callers have prepared/current-item work before this call; this note does not declare those preceding inverses proved.

Shared runtime assumptions are normal Rust collection validity: successful reservation provides capacity for subsequent insertion/push; a fallible reserve error preserves logical contents; deleting/draining elements does not secretly shrink retained allocation capacity; reserved HashMap capacity and ordinary Eq/Hash support replacement/removal without a new allocation. No arbitrary scalar overwrite, forged ID/capacity, data race, continuing execution after panic/UB, or broken allocator is admitted. No allocation success is assumed. For the supplementary edge-byte argument, current nonzero edge Vec backing allocations are disjoint and addressable, as in the explicit ordinary allocation model of [postrepair ledger derivation](2026-10-11-retained-wa3-postrepair-ledger-proof.md). Actual linked runtime/allocator metadata remains unverified.

## 1. Construct the call cases

Actual owner: `candidate_context.rs:2711–2730`. Canonicalization is read-only (`candidate_context_pair`, `2471–2483`; `lib.rs:11423–11436`; intrusion representatives `candidate_intrusion.rs:63–79`). `post_check_context` (`2423–2429`) reads the saved relation context or the already retained discharge residual; it creates no context expression.

1. **None:** returns Ok(None) before any access or mutation.
2. **Equal raw pair:** after read-only canonicalization and the endpoint assertion, `key.pair==pair` returns Ok(Some(parent)). No reservation, dependency, context node, processing assignment or resource sample occurs.
3. **Changed canonical execution pair:** call `State::relation(pair, post_check_context(parent))`; admit `Dependency::Derived { parent, child }`; call `sample_f4_resources(IncomingRoute)`; then return Ok(Some(child)). Each failure propagates immediately through `?`. Returning Ok requires all three operations to finish, including sample publication. Duplicate relation/dependency admissions count as completion; they need not create another record or generation.

The assertion/index preconditions are constructor validity requirements; their failure would be a panic, not the function's Err outcome. The two actual typed callers (`lib.rs:12031–12036,12242–12248`) assign their next processing/current-item/stage only **after** this call returns Ok. `candidate_context_execute` (`2733–2743`) likewise replaces processing only after successful transport and restores that previous value after its later execution. Thus transport's own Err cannot publish its caller's next stage.

## 2. Derive relation reservation/publication inversion

`State::relation`, `candidate_context.rs:2232–2253`, first checks the exact `(pair, context)` key. A duplicate is read-only. For a new key, u32 length conversion and all three reserves (`relations`, `keys`, `pair_heads`) precede the first logical write. A failure at any reserve has changed no relation count, key membership or pair head; earlier successful reservations can nevertheless have changed capacities.

After all reserves succeed, the constructor stores the old pair head in `Relation.previous_on_pair`, appends exactly one Relation, and inserts its key. There is no Result failure between these writes. Therefore the relation append log is also its complete logical inverse certificate; no deduction from endpoint equality is used.

Rollback `1647–1654` drains appended relations in reverse order, removes each exact key, and restores the saved pair head or removes the newly created head. For a fixed pair, the newest record points to the immediately previous head; reverse induction consequently restores the exact head chain, not merely its length. All replacement heads are retained earlier relations. Reserved map capacity remains sufficient while removal/replacement proceeds. The resulting relation length/key set/head map equal C's. No context expression was created by transport, so context count and context interning map stay equal throughout this seam.

## 3. Derive Derived dependency and bundle inversion

`State::dependency`, `2284–2340`, first tests exact dependency membership. A duplicate is read-only and does not advance generation. For a new **Derived** record:

- `next_generation` equals the existing generation; only FunctionPort increments it.
- `invalidations=0`; no source-support validity bit or undo record changes.
- dependency Vec/set reservations precede admission; their failures may retain capacity but append no dependency.
- `edge(parent, child)` runs before dependency Vec/set publication. Thus edge or bundle failure can leave an admitted edge even though the dependency was never appended.
- after edge completion, dependency append, exact membership insertion and same-generation assignment have no further fallible production operation.

This last distinction is covered by the source's own edge log; rollback does not require a dependency record to discover the edge. Test-only publication/AfterInvalidation rejection points are also before dependency append; for Derived the latter has invalidated no support.

`edge`, `2342–2380`, checks duplicate edge membership, reserves the outer map, exact key set, append log and destination Vec, accounts the Vec growth, then pushes/inserts/logs the edge. All three logical edge writes precede the fallible `bundle_edge` call. A fresh temporary Vec is dropped on error before publication. After edge publication, its log entry remains available even if bundle propagation fails.

`bundle_edge` (`2164–2172`) calls `bundle_link` for the parent's retained incidence chain. `bundle_incidence_insert` (`2128–2136`) reserves its set/log/head map before inserting a distinct `(relation,bundle)`, and saves the previous head in each appended record. `bundle_link` (`2138–2162`) uses the append log as its finite work queue: only a previously absent incidence extends it. Propagation may reach existing relations; those changes are still recorded with their own saved heads. A failure after any finite prefix leaves exactly that prefix in the log. No inference merges distinct bundles or source occurrences.

Lazy transport-index activation (`2118–2126`) constructs its index in a local variable. An error drops that variable before field assignment. If a previously absent index is installed, C records None and rollback removes the entire new index. If an index already existed, Derived admission adds no Transport entry to it; checkpoint rollback therefore preserves its existing log/head values. Existing exact dependency witnesses determine the built index; this note does not prove their semantic authentication.

Rollback `candidate_context.rs:1625–1631` reverses appended bundle incidences, removing exact set members and restoring saved heads, before relation records are removed. It then restores/removes the lazy transport index. Dependency rollback `1655–1657` removes exact appended dependency keys. Edge rollback `1666–1674` reverses logged edges: remove the exact key, pop the saved child from the parent's Vec, remove an emptied bucket. Reverse induction on the append log proves the pop assertion and restores every pre-existing edge sequence. Old child relations need not survive relation removal to execute the inverse: it uses retained IDs as values and does not dereference them.

Consequently every partial admission prefix has an exact logical inverse. Relations, dependencies, contexts, bundle incidence/head membership and edge sequence projection return to C. Derived never changed lifecycle generation or processing; rollback explicitly assigns C's generation and processing (`1658,1665`). Under the prefix conditions, these also equal B's named logical values. This derivation does not import normal return of all unrelated semantic inverses: their ranges are empty for the isolated seam. A nonempty real prefix retains its separate owning proof obligation.

### Edge-byte subcase

`edge_bytes` is the sum of nested edge-Vec capacities charged at growth. Under an exact constructor entry census and ordinary disjoint addressable Vec ownership, its postgrowth mathematical sum fits usize. Thus the checked delta/add before edge publication succeeds for native valid growth; this argument is independent of HashMap bucket overhead. A failed reserve leaves no new contents. On rollback, removing a fresh edge bucket subtracts its full retained capacity; popping from a pre-existing nonempty bucket keeps its enlarged capacity and keeps that growth charged. This establishes correctness relative to **current** retained edge storage. It does not establish entry-capacity equality. Arbitrary corrupted edge-byte counters are not source counterexamples.

## 4. Connect the actual session owner, without assuming global inverses

`begin_route_transaction_for` captures `intrusion.begin()` and execution counters (`lib.rs:9134–9194`). Intrusion begin captures effect-algebra checkpoint (`candidate_intrusion.rs:85–97`); that checkpoint captures context checkpoint (`candidate_effect.rs:162–179`). Context checkpoint (`candidate_context.rs:1552–1579`) stores the exact relation/dependency/context and edge/incidence frontiers, generation and processing used above.

An Err in the enclosing transaction reaches `finish_route_transaction`'s error arm (`lib.rs:9234–9237`). Rollback first reverses the store and then calls intrusion rollback (`9370–9374`). Intrusion immediately calls effect-algebra rollback (`candidate_intrusion.rs:103–105`), which immediately calls context rollback (`candidate_effect.rs:181–183`). Thus the context inverse precedes forest restoration, Local cursor checks, GraphState refresh, ordinary row rollback, workspace rollback and late accounting return. Later errors cannot undo the already derived context projection restoration.

For a seam-only route suffix, all earlier effect/context undo ranges are empty, and no extra preceding inverse-success hypothesis is needed. For a general nonempty route prefix, the exact remaining reachability premise is normal return and constructor consistency of that prefix's store/context undo ranges. This packet does not assert it. It also does not claim that the whole rollback returns Ok: the Local/refresh and late accounting owners have independent lemmas. The original route error can be replaced by a rollback error because the outer call uses `?`.

## 5. Stop at the accounting correspondence

The requested exact accounting census is not supplied by the logical inverse above. Two different meanings require distinct evidence:

**Exact numeric pre-call census.** `Checkpoint` (`705–733`) stores frontiers, not the original allocations for relations, dependencies, their maps/logs or pre-existing edge buckets. Relation reservation may grow `relations` and then fail in `keys.try_reserve`; dependency/edge/bundle reservation has the same possibility. Draining removes logical entries but retains these capacities. `State::bytes` (`1921–2005`) charges those current capacities. Therefore no source inverse can derive equality to B's charged bytes merely from equality of counts. Forcing a growing reserve followed by a later real reserve error is a source-permitted local allocation branch, but this lane did not construct an authentic retained source trace realizing it; this is a precise missing correspondence, not a declared source-qualified refutation.

**A correct census of physically retained postrollback storage.** Recomputing `State::bytes` uses current capacities and the edge-byte rule above. Session sample reaches it via effect bytes (`candidate_effect.rs:211–235`), intrusion bytes (`candidate_intrusion.rs:134` onward), and `lib.rs:10601–10630`. But `rollback_route_transaction` restores `execution_counters` from C (`9514–9516`), reconciles only ordinary bound-lane growth, preserves peaks, and returns after workspace reversal (`9666–9700`); it does not call `sample_f4_resources` there. The seam's retained context capacity deltas have no analogous reconciliation/publication in that owner. Thus restored old sampled totals are not proved equal to the recomputed current census.

The post-admission sample itself is transactional in its publication: it prepares cloned counters (`lib.rs:10802–10804`), checks arithmetic, prepares the independent test ledger, and only then publishes ledger/counters (`11083–11085`). On sample Err, no new production counter sample is published; on success a later enclosing error can roll back. This establishes the sample's own failure atomicity, not correct postrollback census publication. The test-only independent `resource_ledger` is not part of `RouteTestCounters` restored here; this lane does not certify its equality after rollback either.

**Exact residual premise/owner:** InferenceSession's rollback/resource-accounting owner must establish the intended census projection after relation/dependency/edge/bundle capacity changes: either actual restoration of the allocation charge named by C, or the existing approved rule for retaining and publishing current capacity charges. The present source correspondence establishes neither exact entry numeric equality nor fresh current-session publication at this seam. An outer owner may later resample; the packet has not established that every requested return path does so. No semantics or supported source restriction is changed to hide this premise.

This is A correctness/accounting at the owning construction/consumer. It needs that exact owner evidence rather than another reconstruction of relation identity. The logical constructor theorem has advanced; the requested accounting theorem and original W/A3 remain OPEN pending primary adjudication and independent review.

## Dependencies, checks, runtime and limits

| Frozen dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `31c66d1bc9cc101c6174424f5f11b7cbeb6eb497448e0a4b09b683adbacb9dd9` |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Reviewed outer rollback premise | `b675d0eece6437b83bfffcb78f261568e6239fa796a0cd7ef9581960d9322bc3` |
| Frozen W/A3 falsifier | `093f2d3ef7ea4d3b206939c5dc8475cfbe793e25f3c01682c5b06d4f2afa59ad` |

Method/checks: bounded exact constructor/consumer and rollback reads, local mutation-prefix/reverse-log induction, plain HEAD/ref reads, exact SHA-256 checks, final leased-note scope/whitespace inspection. Read yulang-proofs skill, actual role/config pins, governing §6, current task and relevant active authority/orchestration/research/economy/concurrency rules. Broad captures truncated initially; decisive regions were reread narrowly. A guessed `candidate_graph.rs` search path was absent; no conclusion depended on it. No Cargo/tests/builds, executable probes, measurements, Git commands/mutations, code/test/shared edits or delegation. Prior notes, including the postrepair ledger note, were not edited.

One leaf; packet started 01:46 UTC, frozen within the ≤20-minute budget. Only short read/hash processes; CPU/RSS unmeasured, zero performance samples. Requested ordinary Sol/high prover lane; observed effective model/effort unknown. No Astra or hot-reload claim. Primary owns independent review and executable verification. This producer does not certify its own result.

One next action: review/apply the exact local logical inverse, then obtain the explicit retained-context capacity/census publication correspondence from the InferenceSession rollback/accounting owner.

## Commit packet

- Exact changed lease: `notes/progress/2026-10-11-context-transport-rollback-proof.md` only.
- Baseline SHA: `6c130940e077853672954640325b034b287a1e96`.
- Changed dependency hashes: none authored by this leaf; frozen current inputs above.
- Claim/review status: unreviewed local constructive inverse under stated prefix/runtime hypotheses; accounting and full W/A3 OPEN. No source-qualified falsifier or self-certification.
- Checks run: source-owner reads/searches, direct case/inverse derivation, hashes and leased-note inspection; no executable verification.
- Proposed checkpoint message: `research: derive context transport inverse and isolate census premise`.
- Proposed shared-record delta for primary/curator: replace this seam's assumed relation/Derived/bundle mutation coverage with the reviewed local log derivation if accepted; retain transaction-prefix reachability, context capacity/census publication and global W/A3 OPEN. No shared records edited.

Artifact frozen after final checks; no further writes planned.

## Independent review adjudication

Fresh compiler-referee review of frozen SHA-256
`f3d240f29a1b2563ba629fefdcf2d00fe792eba090ae9125bf7e0ad8c50979a0` found no
blocking, major or minor findings. It accepts the local logical inverse under
the stated transaction-prefix and runtime hypotheses. It confirms that this
does not prove the real route prefix, retained-capacity census publication or
the whole W/A3 theorem. Apply the local inverse to that parent only as bounded
constructor evidence; keep accounting and original W/A3 OPEN. No executable
verification ran.
