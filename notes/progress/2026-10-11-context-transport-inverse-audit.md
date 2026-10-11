# Candidate context transport: inverse and failure audit

Date: 2026-10-11
Status: independently reviewed bounded source characterization; no constructor-qualified counterexample found. Original W/A3 remains OPEN.
Producer: leaf `/root/context_transport_inverse_audit`; complementary falsification/source method, no delegation.
Baseline: `6c130940e077853672954640325b034b287a1e96`; inspected compiler dependencies equal the `d7e87c637` source hashes recorded in the prior audit.
Exclusive write lease: this note. Budget: one lightweight static pass, at most 20 minutes wall time; no compiler edits, tests, builds, Cargo, executable search or Git mutation.

## Objective and authority

Seek a reachable error after partial relation-transport mutation which escapes the owning route inverse, or a resource sample before undo ownership exists. This examines the atomic transport constructor left unexhausted by [the prior adversarial audit](2026-10-11-retained-wa3-postrepair-adversarial-audit.md), “Exact residual owner and stopping point”; it does not repeat its queue/receipt inventory or ledger arithmetic attack.

Authority: user-approved [private candidate suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md) §6, including exact route rollback and fallible reservation before mutations relying on storage. Accepted approval is “承認して実装を進めて”. The original theorem/quantifiers are [nonterminal composition](2026-10-11-nonterminal-drain-owner-composition-proof.md), “Frozen objects, statement and exclusions” and H1/W, and [retained handoff](2026-10-11-retained-parent-handoff-proof.md) A3/A4. This pass does not replace their arbitrary finite Q/A, valid-stage, committed Running/Ready, original lineage, incidence or source-domain obligations with fresh-only execution.

## Exact claim class and hypotheses

**Bounded characterization:** the inspected transport body and its transitively called relation/dependency/edge/bundle producers provide an identifiable checkpoint inverse for each semantic mutation, including mutations before a later ordinary error. No post-mutation error branch lacking those logs was found in this call cone. This is neither a reviewed theorem nor unconditional rollback certification.

The following premises remain explicit:

1. A route checkpoint exists before entry and reaches its single rollback owner without a hidden commit; candidate intrusion/effect/context objects stay owned. Retained typed-frame updates have their original frame retained before this stage.
2. Entry relations, keys, pair heads, dependency keys, adjacency vectors, edge keys/log, bundle incidence/heads/log and optional transport index are well formed construction records. IDs/frontiers are valid; no other session mutation interleaves. In particular, the edge log suffix identifies the corresponding adjacency suffix in order.
3. Collections satisfy their actual reserve/insert/pop/drain validity and capacity guarantees; reverse replacement of already owned map entries requires no new allocation. The nested adjacency byte census is exact and its post-reserve checked addition is representable. Applicability to the linked runtime is unverified.
4. Other mutations made earlier in the route obey their own inverse owners. The inspected call cone cannot certify those operations, arbitrary scheduler entry states or outer rollback return.

These are construction/runtime premises, not selected new language assumptions. Finding source logs does not prove every admitted initial state satisfies them.

## Fallible-step and undo map

Locators refer to `crates/yu-solver/src/` at the baseline.

| Forward owner / failure point | Mutation before failure and owning inverse |
| --- | --- |
| `candidate_context.rs:2711–2728`, `candidate_context_transport_task` | `None` and unchanged-pair branches return without mutation. Changed-pair branch canonicalizes the task and validates matching canonical parent endpoints, obtains `post_check_context(parent)`, then calls relation, Derived dependency, and the final resource sample. Canonicalization/context lookup here are reads. Invalid IDs/assertions are outside the ordinary `Result` failure claim. |
| `2232–2252`, `State::relation` | Existing key returns its ID. New-ID conversion and reserves for relation/key/pair-head storage precede semantic publication. Publication saves `previous_on_pair`, appends the relation and inserts its key with no later fallible operation inside this producer. `checkpoint.relations` and the saved predecessor reverse the suffix at `1647–1654`; keys are removed and pair heads restored in reverse construction order. A later dependency failure still has that relation record. |
| `2284–2340`, `State::dependency(Derived)` | Duplicate dependency returns without mutation. In this variant no lifecycle generation increment or support invalidation occurs. Dependency vector/key reserves precede `edge(parent,child)`. A failing edge/bundle call can leave edge/incidence records but has not yet published the dependency. Success appends dependency and inserts its key; `1655–1658` removes the dependency suffix and resets generation. |
| `2342–2376`, `State::edge` | Duplicate edge returns unchanged. Outer map/key/log reserves and nested adjacency reserve precede publication. `edge_bytes` checked arithmetic is **after** nested reserve, before adjacency push. On success push, map insertion for a new parent, edge-key insertion and edge-log append occur before fallible `bundle_edge`. Thus a bundle failure already has exact adjacency undo. `1666–1674` removes keys, asserts reverse `pop()==child`, and drops an empty adjacency while subtracting its retained capacity. Growth surviving in an old nonempty adjacency remains charged rather than pretending capacity shrank. The byte-error seam is discussed below. |
| `2164–2174`, `bundle_edge`; `2138–2162`, `bundle_link` | May fail after earlier incidence propagation. Every successful incidence insertion reserves its set/log/head storage first (`2129–2136`), retains `previous_on_relation`, and appends the log. `1625–1629` reverses that suffix and restores/removes heads. Propagation uses the growing incidence log as its work queue; duplicate admission adds no unlogged incidence. |
| `2118–2127`, optional bundle-transport activation | Builds its index locally from retained Transport dependencies; failed build drops the local index. Successful activation publishes `Some(index)`. Checkpoint stores prior optional index length (`1563`); `1630–1631` reverses appended records for prior `Some`, or drops new activation for prior `None`. `BundleTransports::insert/rollback`, `283–296`, retains and restores predecessor heads. Derived dependency itself does not append a Transport record. |
| `2727`, final `sample_f4_resources(IncomingRoute)` | Runs after relation/dependency/edge/incidence logs exist. `lib.rs:10439–10645` may return an accounting error while computing retained resources; this does not erase the active journal. Its candidate census includes live intrusion/context capacity plus intrusion undo. Failure propagates through the route finish owner. No earlier sample exists inside these transport producers. |

The test-only `DependencyPublication` failure hook runs before the edge call; `AfterInvalidation` runs after the edge/bundle work and before dependency append. For Derived there is no invalidation, but the second hook can still fail after edge/incidence publication. Both follow the above ownership map. These hooks were read, not executed, and are not witnesses of an ordinary source-triggered failure.

## Reverse ordering and route correspondence

`lib.rs:9128–9188` installs `journal.intrusion = state.intrusion.begin()` before publishing the active route journal. `candidate_intrusion.rs:87–115` captures the effect checkpoint and begins rollback with `effect_algebra.rollback`; `candidate_effect.rs:162–182` captures the context checkpoint and begins reversal with `context.rollback`. Thus the constructor suffix frontiers come from route entry, rather than being inferred after mutation.

Within context rollback, bundle incidence and transport state reverse before relation destruction; relations reverse before dependency-key removal and adjacency reversal. The latter consumers use retained numeric keys/log records and do not dereference removed relation objects. For a sequence of new relations on one pair, reverse predecessor restoration reconstructs the former head. For several edges on one parent, reverse edge-log order reconstructs its adjacency suffix; no dependency record is required to reverse an edge whose later bundle propagation failed.

The retained stage at `lib.rs:12162–12208` calls `prepare_nonterminal_drain` before transport. `candidate_context.rs:1748–1764` retains the original frame in undo before replacement. `lib.rs:12242–12248` writes the child relation/current item and moves to Context only after transport succeeds. Consequently a failed transport does not publish that stage advancement. The synchronous drain similarly retains popped work before transport (`lib.rs:12005–12046`); this is bounded caller evidence, not proof of all call-site/scheduler states. `candidate_context_execute` calls transport again and restores its temporary processing value around execution (`2733–2743`); the remainder of context execution is outside this lease.

`lib.rs:9197–9238` sends every `Err` through `rollback_route_transaction`; `9369–9389` reverses intrusion/context before Local validation and graph refresh. Those later fallible steps and late bound accounting remain separate premises. The test-only retained typed driver (`12297–12304`) starts RetainedResume and uses this same finish owner. The pass establishes actual ownership edges, not a new production suspension driver.

## Precise untouched premise and stopping point

The decisive remaining local accounting seam is `State::edge`: after `entries.try_reserve(1)` grows an **existing** adjacency, its checked byte addition can syntactically return `Err` before any new edge log or updated byte charge. In that branch rollback does not shrink the grown old adjacency or repair `edge_bytes`; exact census would be lost **if the arithmetic failure were constructor-reachable**. For a fresh local adjacency, that allocation is dropped on error, so the same argument does not produce retained uncharged capacity.

No constructor-qualified arithmetic-overflow witness was established. Assigning an arbitrary near-MAX `edge_bytes` would assume the missing reachability premise and is not a falsifier. The needed bridge is: every admitted entry has `edge_bytes = Σ capacity(adjacency) × size_of(RelationId)`, and actual disjoint owned adjacency buffers make the successful reserve's resulting total representable. The forward success and reverse-empty removal preserve that equality locally; failure of the checked addition is excluded only after the allocation/census premise is established. The reviewed late-bound model R provides useful Vec ownership assumptions, but it does not automatically prove this context census or the map/log entry predicates.

Accordingly this audit stops with no concrete witness and an exact remaining premise. It adds inspection of the real atomic producer to the prior outer inverse map. It does not turn a source absence search into theorem closure or create another toy transition checker.

## Independence, coverage and resources

Evidence comes from actual forward and reverse compiler source, independently of a supplied transition model. There is no independent executable oracle, seed/range, enumeration or mutation run. Shared assumptions are the explicit entry construction invariants and actual Rust collection/allocation behavior. Ordinary reservation failures, later bundle propagation failures, final sample failures and the two static test hooks are covered by the inspected ordering. Panic, corruption, invalid IDs, allocator-contract violation, all-source scheduler reachability, independent atomic context execution, intrusion settlement, other effect/store producers, incidence, lifecycle, source/SCC publication, complete Call meaning, hygiene, soundness, principality and cutover are omitted.

Checks run: required rules/skill and exact governing-note reads; bounded `rg -n`, `sed -n`, `cat`; read-only HEAD/status, scoped `git diff 6c130940e -- <dependencies>` (empty), and `sha256sum`. Several broad captures truncated; the contract, prior audit and precise forward/inverse bodies were reread narrowly. No tests/build/Cargo/formatter, source/test edit, scratch experiment, Git mutation or child launch. One static pass, short read/hash processes, no sustained compute, zero performance samples; CPU/RSS/process-total and exact elapsed wall time unmeasured, within the 20-minute ceiling. Runtime model/effort metadata unknown.

| Frozen dependency | SHA-256 |
| --- | --- |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `lib.rs` | `31c66d1bc9cc101c6174424f5f11b7cbeb6eb497448e0a4b09b683adbacb9dd9` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |
| `candidate_scheme.rs` | `b15d72a5be0f82b2dba37b12fdc3e11a555253ff92ae7aa615b05aaa00380768` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Prior adversarial audit | `3af82c5fece63b74390c795ba8c56d678969e2c4f11e0b9c7feef9ef0d8a8f0e` |
| Original composition | `4344694f4b8a8c4a225aae83d3c39fcf242f92c2ff32f0ae059d84ad85ff9222` |
| Retained handoff | `052ac8e6499b116f4ec7adc8e9c935ee04f02c8a27419428a4659514a7c12357` |
| Late-bound proof, allocation-model section only | `bd87153bbb2e0abb72a56430d30ad3bb84c16b7e21bbb27b4875917a7770eca4` |

One recommended next action: the primary gives the constructive owner this producer/inverse map and requests the exact entry-predicate plus post-reserve adjacency-census bridge, then assigns fresh independent review of the frozen pair. Keep original W/A3 OPEN.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-context-transport-inverse-audit.md`.
- Baseline SHA: `6c130940e077853672954640325b034b287a1e96`.
- Changed dependency hashes: none authored or observed against baseline; frozen inputs above.
- Claim/review status: unreviewed bounded source characterization and exact conditional failure seam; no constructor-qualified witness, independent certification or parent closure.
- Checks already run: focused forward/inverse/caller reads, baseline dependency diff and hashes, leased-note whitespace/scope inspection; no executable verification. Primary owns verification/review.
- Proposed research-checkpoint message: `research: map context transport failure and rollback ownership`.
- Shared-record deltas intentionally left to primary/curator: record this atomic producer coverage and the exact adjacency census/entry-predicate bridge; preserve semantic inverse totality and original W/A3 OPEN. No shared records edited.

Artifact frozen after final lease/dependency checks. No further writes planned.

## Independent review adjudication

Fresh compiler-referee review of frozen SHA-256
`3ccdb490f613187623bf165cb2521cc27dd42191d64ea61290b34347d4c6b733` found
no blocking, major or minor findings. It confirmed that the transport producer
and rollback map is accurate within scope, and that a post-reserve checked
`edge_bytes` failure would retain unlogged growth if constructor-reachable.
No constructor-qualified witness or census invariant was established. Runtime
allocation behavior, all-history entry predicates and global W/A3 remain OPEN.
No tests or executable probes ran.
