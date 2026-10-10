# Canonical bound fibers: constructive lifecycle audit

Date: 2026-10-10
Status: independently reviewed conditional storage derivation; attempted replay obstruction rejected and withdrawn; restoration coverage remains open; no gate, soundness, or production-conformance promotion
Assigned baseline: `1007224e2e7e6efab1590bd88c54bcb0a1fe8ff6`
Baseline identity: primary revalidated the eight listed source/design dependencies byte-for-byte against this commit; they are unchanged at current HEAD
Exclusive output lease: this file only
Producer: `/root/bound_fiber_proof`, leaf; no descendants
Requested runtime: `gpt-6.1-sol` / `high`; observed model and effort: unknown (no effective runtime metadata exposed to this leaf)

## Objective and frozen statement

Audit the claim: every physical live bound used by opposite replay has an attached relation fiber at its exact canonical `BoundKey`, including insertion/restoration through a stale recorded parent-copy endpoint after SCC equality.

Fix one candidate session with `shadow-apply-candidate` enabled and its candidate graph present. Let `c_s(e)` be the actual `canonical_extrusion(e)` in state `s`, and let

```
K_s(o,p,b) = BoundKey(c_s(o), p, c_s(b)).
F_s(k) = the relations enumerated by context.bound_relations(k).
```

Positive selects a lower bound; negative selects an upper bound. Physical bounds are exactly the four direct/exact vectors in each Value or Effect row. The scope includes every occurrence in these vectors, including duplicates and self bounds retained by equality; it is not limited to distinct endpoints or one selected relation per key. Only the canonical owner's vectors are consumed by `candidate_opposite_count` / `candidate_opposite_bound`; retained vectors at an aliased copy remain rollback storage.

The storage statement **C** is: for every replay-consumed physical bound `(o,p,b)` in the inspected transition envelope, `F_s(K_s(o,p,b))` is nonempty at the replay boundary. Existing multiple fibers remain distinct; this existential storage property does not assert that one arbitrarily selected fiber represents all derivations.

The source/operational bridge additionally needs **R**: the keys actually passed to `candidate_context_replay_impl` identify the complete corresponding lower and upper fibers in that state. C alone does not imply R. This distinction preserves the original claim rather than silently interpreting successful storage as successful activation or complete replay.

Hypotheses for the conditional derivation of C:

1. Initial replay-consumed vectors are empty, or their canonical keys already have fibers. This is an explicit initial-state hypothesis, not a proved claim about every compiler initialization path.
2. All subsequent physical-vector additions in this envelope pass through `candidate_insert_bound_impl`; representative changes pass through successful `merge_candidate_rows` and its canonicalization before replay. This envelope is the inspected candidate insertion/extrusion/intrusion/restoration route, not arbitrary legacy mutations in `lib.rs`.
3. Calls respect actual valid endpoint kinds, valid row/relation indices, and the existing idle-worklist assertion on restoration. The forest maps remain well formed. Operations either succeed or use the inspected matching route transaction to roll back failure before another consumer runs.
4. No external mutation interleaves the synchronous Rust methods. Allocation/resource errors stop the current route at their actual `?` boundaries.

No hypothesis grants relation presence at a new insertion key: that fact is derived below. No hypothesis forbids stale endpoints, equality, recursion, or ordinary inference. For R across a restoration loop, representative stability is **not** assumed; the code itself permits an SCC drain inside that loop.

Exclusions: source-program reachability of the operational witness, all compiler initialization/mutation paths, arbitrary contextual termination, complete Call, effect hygiene, residual lineage correctness, provider/witness correspondence, global soundness, and principality are not established here. The audit does not alter any of those requirements.

## Authority and actual owners

The governing source is `notes/design/2026-10-10-contextual-attachment-admission-design.md` §4, specifically Bound insertion, Opposite replay, SCC intrusion, and Rollback. It requires bound contexts/origins, ordered Cartesian replay with shared-input identity, transport through actual qualifying recorded pairs, and route rollback. §3.1 keeps attachment-member grouping separate from row equality. No new semantic decision is proposed.

The role contract and rules were read: `.codex/agents/prover.toml`, `.codex/config.toml`, `rules/agent-orchestration.md` (including Proof delegation and decomposition and Model routing and Astra escalation), `rules/research-lab.md`, `rules/design-authority.md`, `rules/compiler-engineering.md`, `rules/git-concurrency.md`, and `rules/orchestration-budget.md`. The `yulang-proofs` skill was applied. Current-task/lab and design-index slices were consulted only as locators; they do not replace the governing source.

Actual transition ownership:

| Source | Inspected functions / relevant anchors |
| --- | --- |
| `candidate_extrusion.rs` | `candidate_extrude` (one-sided link and copied bounds, lines 123, 303–324); `candidate_insert_bound`, `candidate_insert_bound_without_capture`, `candidate_insert_bound_impl` (389–531); `candidate_opposite_count`, `candidate_opposite_bound` (534–593); `candidate_restore_bound` (599–644); `candidate_replay_bound` (646–693); `candidate_apply_value`, `candidate_apply_effect` (696–751) |
| `candidate_effect.rs` | `BoundKey`; `candidate_bound_origin` (327–369); `candidate_transfer_bound_origins` (436 onward); context checkpoint/rollback forwarding (161–179) |
| `candidate_context.rs` | `State::attach`, `bound_cursor`, `bound_entry`, `bound_relations` (1527–1564); `candidate_context_pair`, `candidate_context_source` (1589–1615); `candidate_context_execute`, `candidate_context_bound` (1803–1910); `candidate_context_replay_impl` (1930–1994); `candidate_context_canonicalize_bounds` (1996–2014); `candidate_context_transport_witness` (2052 onward); `State::checkpoint`, `State::rollback` (1059 onward) |
| `candidate_intrusion.rs` | `State::rep`, representative lookup; `retain_extrusion_parent` (171–222); `settle_candidate_intrusion` (358–512); `merge_candidate_rows` (513–610); `State::begin`, `State::rollback` |
| `lib.rs` | `canonical_value`, `canonical_effect` (11327–11341); `constrain_live_item`, `constrain_live_item_with_inferred_entry` (11799 onward; SCC drain at 11841); candidate dispatch in `apply_value_task` (13016); `with_route_transaction`, both row journals, `rollback_route_transaction` (9155–9445 inspected slices) |
| `candidate_scheme.rs` | captured-owner replay loop and fresh transport immediately before `candidate_restore_bound` (997–1033); no complete source-generation audit |

The test `third_owner_incoming_bound_survives_parent_copy_intrusion_and_rollback_retry` in `candidate_context_tests.rs` (1366 onward) was read as an authored regression: it covers Value/Effect and restoration before/after a completed merge. It was **not run** and supplies no executable result here. It does not cover a two-pair representative change inside one restore loop.

## Conditional derivation of canonical storage coverage

**Insertion.** `candidate_insert_bound_impl` first computes `owner = c(owner)` and `bound = c(bound)` (422–423), then calls `candidate_bound_origin(BoundKey(owner,p,bound), None)` before any vector push. With the graph present, the origin function always calls `candidate_context_bound`, even when the separate origin-key record is already present. `candidate_context_bound` constructs the canonical endpoint pair, selects its retained parent/source context, records a Derived dependency, and calls `State::attach` at the *supplied bound key*. Since insertion supplies the already canonical key, successful attachment gives `F(K) != ∅`. `attach` either finds the same relation already in that exact fiber or prepends a linked entry. Only after that successful return does insertion push to its selected physical vector. Thus any successful new physical entry has its canonical fiber before publication to a replay consumer. Duplicate entries do not erase any fiber. Capture registration is later and does not change representatives.

**Stale endpoint after a completed merge.** If a supplied copy `b` now represents parent `B`, insertion computes `c(b)=B` before attaching and before storing it. If the owner is stale too, both are canonicalized together. `candidate_restore_bound` invokes this insertion first, then canonicalizes both local endpoints before starting opposite replay. Therefore a stale endpoint supplied *after equality has completed*, with no further representative change before the lookup, creates and reads `BoundKey(c(owner),p,B)` directly. This is derived from the constructor; it does not assume the older stale key exists.

**Extrusion and ordinary application.** The inspected extrusion links/copies and `candidate_apply_value` / `candidate_apply_effect` all call this same insertion constructor. Transport subsequently adds each source fiber with its witness; it is not necessary to invent a replacement identity fiber from IDs to prove nonemptiness. This derivation does not claim that the constructor's initial fiber alone captures all required contexts.

**SCC equality.** `settle_candidate_intrusion` chooses merges only from retained parent records whose current copy and parent occupy the same computed SCC. `merge_candidate_rows` appends both copy sides into the parent using the same insertion constructor and transfers source fibers with `TransportReason::ParentCopy { parent_index }`. It updates the representative forest, then calls `candidate_context_canonicalize_bounds` before replay. That method visits the entire pre-call bound-entry prefix, computes `to = K(from)` using the new representatives, and transports every entry whose key changes. Historical entries are preserved. This covers third-owner bounds naming the merged copy as well as bounds owned by that copy. At the successful canonicalization boundary every old physical entry's new canonical key has a fiber; every newly appended parent entry had one before the representative update and is included in that prefix. Only afterward does merge enumerate parent lowers and invoke replay. Induction establishes C for these successful merges without restricting SCC shapes or row orientation.

**Rollback.** Context checkpoints retain the bound-entry length and replay log length. Reverse rollback restores every old head in `bounds`, removes newly created fibers/relations/dependencies, and restores replay frontiers. Intrusion rollback restores forests and then the old generation/dirty state. The matching outer route journal restores all four physical vector lengths and row metadata and truncates new rows. At the completed rollback boundary the pre-route storage state and canonical maps are recovered, so a pre-route C hypothesis is preserved. This is a boundary argument; an intermediate point inside rollback is not a publication boundary. Failure without a matching transaction is excluded rather than falsely certified atomic.

**Replay under stable representatives.** `candidate_replay_bound` canonicalizes owner/item and only enqueues induced items inside its loop; its inspected publish callback does not drain the solver. With stable representatives the supplied keys are precisely K for the inserted and existing sides, so C supplies nonempty heads. `candidate_context_replay_impl` then enumerates the two frontier rectangles with recorded lower/upper order; incoming restoration instead starts both frontiers at `None`. This supports a conditional activation bridge under stable representatives. It is not a proof of R for restoration across its nested drains.

## Attempted obstruction: representative changes inside restoration (retracted)

`candidate_restore_bound` saves canonical `owner`, canonical `bound`, and `count` once at 612–614. Each publish callback invokes `constrain_live_item` at 637–639. That consumer drains the worklist and runs `settle_candidate_intrusion` whenever the worklist is empty (`lib.rs:11838–11843`), so representatives can change before the next loop iteration. This makes a frozen opposite-bound count worth checking, but does not alone prove an omitted required comparison. The attempted trace below incorrectly claimed a missing replay fiber and must not be used as a counterexample.

The producer proposed this source-operational trace using actual candidate constructors, no synthetic context transitions. It is **not an executed test or a source-program counterexample**, and independent review found a contradiction in its claimed miss. Let the proposed endpoints be distinct Value rows; `+`/`-` below denote the bound side.

1. Create parents `B` and `O` at level 2, then use actual positive extrusion to level 0 to create `b` from `B`, followed by `o` from `O`. This retains actual parent records in the order `(b,B)` then `(o,O)` and inserts `B - b` and `O - o`. The selected positive copies initially have no lower bounds. No arbitrary non-parent equality is used.
2. With an idle worklist, use `candidate_insert_bound` to insert `b - B`, `o - O`, and `o - TopNegative`. These insertion calls retain all fibers and leave intrusion dirty. Both actual parent/copy pairs now qualify in SCCs. This is an admissible API state; generation of this exact pending state from ordinary source/scheme capture has not been inspected.
3. Call `candidate_restore_bound(o,+,b,occurrence,cause)`. It inserts `o + b`, attaches `BoundKey(o,+,b)`, and freezes local `bound=b` and `count=2` (one direct upper O and one exact upper TopNegative).
4. Iteration 0 reads `o - O`, creates the ordered replay `b <: O`, and drains it. With `b` at level 0 and `O` at level 2, `candidate_apply_value` selects owner `O`, positive lower `b`, and inserts `O + b`; this does not destroy either qualifying parent/copy pair. On the empty-worklist boundary, the actual parent-record order merges `b→B` first and `o→O` second. All allocations/drains in this description are assumed successful; no finite run was performed.
5. The first merge transports `BoundKey(o,+,b)` to `BoundKey(o,+,B)`. The second reads the now-canonical lower B, inserts `O + B`, and transports to `BoundKey(O,+,B)`. It also transfers both o uppers. Since O already physically owns the extrusion upper o, its direct uppers now contain old o and transferred O, followed by exact TopNegative. Canonicalization yields canonical self-upper fibers. The canonical lower fiber exists, so C continues to hold.
6. Returning to outer iteration 1, `candidate_opposite_bound(o,+,1)` may read the changed canonical owner's vector. The producer asserted the next inserted key is `BoundKey(O,+,b)` and that it had no fiber.
7. That assertion is false. In step 4, processing `b <: O` selects positive insertion `O + b` before either merge. `candidate_insert_bound_impl` attaches exactly `BoundKey(O,+,b)` before publishing the physical bound. Later canonicalization preserves this historical fiber and adds canonical transport. Thus the proposed first absent-fiber lookup cannot occur. The frozen loop count may skip an entry after the vector changes, but this trace does not establish that an obligation is skipped: merge itself replays retained lower bounds against the merged owner's current upper bounds.

The compiler-referee review found no other mathematical or source-bridge finding in its assigned scope, but classified this asserted miss as a **major** artifact error. Its required repair was to retract the absent-fiber conclusion or account for every insertion induced before and during the drain. This section records that repair. Whether the changed vector/count can omit any required *incoming-use* replay or diagnostic despite merge replay remains open; the direct trace above no longer supplies evidence either way. Source-program reachability also remains separate.

## Obligation economy and next evidence

Canonical storage coverage is constructional evidence under the stated hypotheses. The proposed trace did not establish a replay omission. The next investigation should determine whether every bound and incoming-use obligation remains covered when one restoration callback drains intrusion and changes the owner's opposite-bound vector; it must account for the merge's own replay before alleging an omission.

There was one constructive preservation derivation followed by a different direct consumer audit; no repeated equivalent proof loop or Astra escalation occurred. A fresh compiler-referee review found one major contradiction in the proposed absent-fiber witness. The primary repaired it; delta review closed that finding and independently accepted C in the stated scope. The remaining work is to determine whether restoration's changed vector/count can omit any incoming-use obligation after accounting for merge replay. Source reachability and lifecycle closure remain separate.

## Checks, coverage, resources, and commit packet

Checks actually run: bounded `cat`, `sed`, `rg` source/rule reads and `sha256sum` of the direct dependencies. No tests, builds, executable solver probe, benchmark, Git command, configuration change, or descendant launch ran. Shell tools were short-lived read/hash operations; zero Cargo processes and zero measurement samples. Aggregate CPU/RAM and effective model/effort were not observed. The note is the only write, and writing stops at handoff for frozen review.

Filesystem SHA-256 dependencies observed during this audit (these are not Git blob IDs; the primary compared them byte-for-byte with the pinned baseline):

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_extrusion.rs` | `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a` |
| `crates/yu-solver/src/candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| `crates/yu-solver/src/candidate_context_tests.rs` | `d543106be87d47cb0c06799e6c543cc7b7b414cffbfc224aa2c5bb07d0d83647` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |

Commit packet:

- Exact leased path: `notes/progress/2026-10-10-canonical-bound-fiber-prover-audit.md` only.
- Baseline: `1007224e2e7e6efab1590bd88c54bcb0a1fe8ff6`; the primary confirmed all eight listed source/design dependencies are byte-identical between that revision and current HEAD.
- Dependency changes: none made by this leaf; current hashes listed above. Changed-against-baseline hashes are unknown under the no-Git contract.
- Claim/review status: independently reviewed conditional storage derivation C; the proposed source-operational obstruction was retracted after one major finding and its delta review passed. Restoration coverage R, source reachability, and gate closure remain open.
- Checks already run: source/rule reads and hashes only; all executable verification intentionally deferred to the primary's verification owner.
- Proposed checkpoint message: `research: audit canonical bound fibers and restoration replay across SCC drains`.
- Proposed shared-record deltas for the primary/curator: record canonical insertion/equality storage coverage as conditional evidence; keep restoration activation/replay completeness open at `candidate_restore_bound:632` / nested SCC drain; distinguish stale endpoints supplied after a completed merge from endpoints becoming stale during one restore call; retain source-program reachability and executable confirmation as unverified. No shared record was edited.
