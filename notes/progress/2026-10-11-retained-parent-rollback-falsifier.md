# Retained parent rollback: owner and byte-sum falsification audit

Date: 2026-10-11
Status: unreviewed research checkpoint; bounded source characterization and conditional arithmetic derivation. No theorem closure or production certification.
Producer: leaf `/root/retained_rollback_falsification`; no delegation or Git authority.
Exclusive lease: this note only; 30-minute static-work ceiling.
Baseline HEAD: `146025ddcafeeae412d9a8b8da5dda536d30f250`, with the pinned worktree inputs below.

## Objective and governing claim

Attack the original parent composition's H1/W failure premise at two specific early returns: Local owner validation and `GraphState::refresh_bytes` inside `rollback_route_transaction`, before retained Q/D workspace reversal. Seek a constructor-valid admitted failure leaving rollback incomplete, or identify the exact premise needed to exclude it. This complements the primary's constructive prover; it does not repeat the acknowledgement-prefix proof.

Authority: [private candidate suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md) §3 (retained ownership), §6 (one transaction and exact failure rollback); §4 incidence obligations remain separate. Accepted user approval is “承認して実装を進めて”. Preserve [original composition](2026-10-11-nonterminal-drain-owner-composition-proof.md), “Frozen objects, statement and exclusions” and H1–H5, and [handoff derivation](2026-10-11-retained-parent-handoff-proof.md), A3/A4. The [source bridge](2026-10-11-retained-parent-handoff-source-bridge.md), “Undo, capacity and failure reconciliation”, explicitly leaves the targeted owner/arithmetic envelope open. No selected language meaning or original theorem quantifier changes here.

**Result:** no constructor-valid witness found in the traced synchronous Local driver, closed Local script, or retained Local step. The Local owner check is excluded by their concrete ownership control flow. The refresh check has a conditional exclusion argument based on disjoint addressable collection allocations, with its runtime/library premise stated below. This is narrower evidence for two sites, not a proof of all semantic journals or the original W theorem.

## Actual failure order

At the pinned `lib.rs:9199–9238`, operation failure invokes rollback and propagates a rollback error through `?`. In `9339–9389`, rollback takes the journal and first restores the store, then calls intrusion → effect → context rollback. Context rollback restores old F, restoration and replay snapshots, including destination, waiting slot and receipt (`candidate_context.rs:1579–1614`). Only afterward does the Local cursor use `last_mut` (`lib.rs:9377`) and refresh run (`9389`). Retained Q/D reversal is later (`9670–9672` and `rollback_workspace:12744–12782`).

Thus a hypothetical error at either targeted site would leave **Q/D and later row/cache/counter cleanup** unapplied; F/slot/receipt inverses have already run. Describing those earlier inverses as unapplied would misstate the source. Taking and then dropping the route journal at an early `?` would indeed prevent retrying the remaining inverse sequence. This ordering makes the exclusion premise material.

## Owner-loss attack and source exclusion

Let a route checkpoint contain `Some(cursor)`. Its constructor is `begin_route_transaction_for` reading the last Local frame (`lib.rs:9136`), so a Local exists at entry. Enumerating `local_use` writes across `crates/yu-solver/src` gives:

- Initial construction reserves and pushes a frame (`candidate_scheme.rs:1368–1378`); initial failure can retain the added capacity, but a route starting empty has `candidate_local_use=None`, so rollback clears rather than validates a last frame.
- Synchronous Local stepping pops its frame, calls `step_candidate_local_use`, pushes the same frame, **then** propagates the result (`1393–1397`). The closed script's FailOne uses the same ordering (`1434–1437`). No exposed pause/error return occurs while the frame is popped.
- Retained Local restoration execution keeps its one unfinished Local in the vector (`1467–1486`). Its fallback pop path likewise pushes before `result?` (`1491–1494`). Entry rejects an active transaction, a vector length other than one, or a completed frame.
- `commit_local_use` is the only completed-frame removal (`229–237`); `finish_route_transaction` invokes it exclusively on the successful branch (`lib.rs:9220–9222`). It cannot precede that route's error rollback. Rollback itself clears only when the checkpoint had no Local.
- `start_candidate_graph` is the only replacement assignment found; production calls it during session initialization (`lib.rs:10118–10123`). The traced Local/replay/typed-drain routes do not call it. Typed drain and restoration primitives do not clear/pop the Local vector. The generic test resume closure is not an authority for arbitrary owner-deleting callbacks.

Induct over completed finite driver calls, retaining the same graph/frame until successful commit. Every fallible return with a saved cursor has restored its temporarily moved frame or never moved it; therefore its vector is nonempty at `last_mut`. This excludes **missing last owner**, the only error generated by that expression. It does not claim that a last-frame presence check alone validates arbitrary owner substitution, nor establish a future general scheduler's ownership.

The smallest attempted countertrace is one pre-existing Local, pop it, execute one failing primitive, return without push. It is discriminating but **not admitted**: every inspected pop owner pushes before inspecting failure. Explicitly calling `local_use.clear()`/`start_candidate_graph` from an unrestricted synthetic callback would destroy the constructor invariant and is not a source-qualified witness.

## Byte-sum attack and explicit conditional derivation

`refresh_bytes` (`candidate_scheme.rs:238–260`) sums five outer vector capacities and, for each live graph/route/frame, its owned graph buffers, route rows and FreshUse buffers. `Graph::bytes` (`214–225`) and `FreshUse::bytes` (`141–148`) use capacities times the exact element types, including `(K,V)` for HashMaps. Every charge is nonnegative. Scratch, orchestration, historical peaks, external evidence-storage bodies and old tracked `retained_bytes` are **not** added. A corrupted high counter therefore cannot directly cause this refresh's overflow.

Source-established structural premise S: each charge identifies one owned collection buffer and none is counted twice. Outer `Vec<LocalUse/FreshRoute/LocalFreshRoute/Option<Graph>>` charges inline element storage; the nested charges refer to separate Vec/HashMap storage. Graph/FreshUse fields own their containers rather than alias a shared buffer. Publication moves the graph/rows; Local-route replacement empties the retained old allocation and keeps it only in journal undo until rollback restores it. At refresh, that journal allocation is neither separately charged nor shared with `state.local_routes`. No unsafe raw-buffer constructor, `set_len`, or aliasing operation was found in `candidate_scheme.rs`.

**Runtime premise R (explicit, not a new source restriction):** for this concrete execution, a nonzero Vec allocation backs `capacity*sizeof(T)` bytes; a HashMap allocation backs at least `capacity*sizeof((K,V))` bytes; these live owned allocations occupy disjoint non-null byte addresses representable by `usize`. All charged element types contain nonzero data; zero capacity charges zero. This is ordinary allocator/collection validity, not an assumption that a resource sample or refresh succeeded.

Under S/R, index each charged buffer by i. Let `c_i` be its mathematical charge and `a_i` the size of its live allocation. Then `0 <= c_i <= a_i`; disjoint non-null byte addresses give `sum a_i <= usize::MAX`. Consequently each multiplication fits, and every nonnegative prefix of the refresh sum is at most `sum c_i <= usize::MAX`. Every `checked_mul`/`checked_add` succeeds. Refresh itself performs no allocation. Allocation failure before a route mutation and retained spare growth after failure do not invalidate this argument: only buffers actually still owned at refresh enter the sum.

The independent arithmetic attack chooses individually representable capacities whose charges sum above `usize::MAX`. It isolates the check, but would require more disjoint charged backing bytes than R permits. Capacity integers alone are not constructor-valid allocations. No such witness was promoted, and no huge allocation experiment ran.

Supporting local library reads independently support the collection part of R: the installed stable std HashMap wraps hashbrown; its library lock names hashbrown 0.16.1. The cached 0.16.1 map stores `RawTable<(K,V)>` (`map.rs:185–188`); raw layout reserves bucket count times tuple size plus controls, rejecting layout overflow (`raw/mod.rs:204–236`); table capacity is items plus growth allowance (`1358–1360`). Installed RawVec source bounds actual capacity/layout and rejects oversized growth. These reads are **not verification of the compiler/stdlib binary actually used by the primary**, nor a proof of allocator correctness or optimizer allocation materialization. The exact remaining arithmetic premise is R's applicability to that execution. No all-platform abstract-memory claim is substituted for it.

## Coverage, omissions and next action

This is one bounded static falsification packet with two different attacks: owner loss and arithmetic overcharge. No executable model/oracle, seeds, numeric ranges, mutations, builds, tests, Cargo or probes ran. Source constructors/call sites and standard collection layout are the evidence; shared assumptions are Rust ownership, valid collections/allocator, and the original primitive/journal hypotheses. Reading fixture bodies is caller evidence only. The primary-reported drain-entry test failure was not analyzed or used as a result here.

Still unverified: general retained scheduler, intrusive corruption/panics, allocator/runtime applicability, all semantic undo invariants, later accounting-error returns, global retained-allocation equality, lifecycle invalidation/recomputation/publication, §4 interference and authentic §7 coverage. In particular, later `accounting_error` can return an error **after** workspace reversal; this packet does not prove it absent or show complete rollback by studying these two earlier sites. The original parent gate remains OPEN; this output is not an independent review of the producer proof/source bridge.

One recommended next action: primary gives a fresh compiler-referee this frozen note and actual runtime/library identity, asking whether S/R and the traced caller inventory justify removing these **two specific** early-return qualifications from the current private-owner bridge. Keep the full W/semantic/lifecycle obligations distinct and OPEN.

## Frozen inputs and resource use

The initial rehash matched every packet input. During pre-freeze revalidation `lib.rs` changed; the leaf notified the primary and reread finish/early rollback/workspace regions. Those relevant visible regions retained the same control flow. The primary identified the delta as a cfg(test)-guarded `incoming_sample_trace::event` for workspace-undo Vec capacity growth, with rollback lines/order unchanged. This is unrelated test trace instrumentation; this leaf does not independently certify that instrumentation or its test result.

| Dependency | SHA-256 at initial read |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `c0d8a21567cad455e41e644501bc06406c37efb1aef60792451161cd3546af50` |
| `candidate_context.rs` | `1b67fa5bab89e4b6d06ca0cd54989ad8f00406962b081e45555b1708ec06932b` |
| `candidate_extrusion.rs` | `a76979f01feaf76ffa351625b0443802fca3e6e2b0288b55e274d7538ae22ead` |
| `candidate_scheme.rs` | `b15d72a5be0f82b2dba37b12fdc3e11a555253ff92ae7aa615b05aaa00380768` |
| `candidate_context_tests.rs` | `397eade3d5a8aae946dd6929aa75cd2424d7b0a0f5067b6cb0e7428d0384a1b9` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Original composition | `fed59c7525595f3d674aaf7c011362267ae54e0ad5ccae920abaaf60bbcf089a` |
| Handoff derivation | `052ac8e6499b116f4ec7adc8e9c935ee04f02c8a27419428a4659514a7c12357` |
| Handoff source bridge | `25e114ca4954ec7ac9672df632c0674f36d9589fb0167a7e051b5e9173bd45e3` |
| `candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |

Supplementary external source snapshots (read-only, actual compiler linkage unknown): installed library Cargo.lock `24ee3436f747470180e01a14bb9dea54eba96be15f65ab0407922a7132de84b4`; installed RawVec `76011c902ab137f3c1ab91432133d1f4ff6038e33fa60bf62a5e325bd12981a4`; installed std HashMap `809f1f8ee73d80b575c76865be9d2e5dc1f1f188d4db2d1180ab7769568a06fd`; cached hashbrown-0.16.1 map `2f42092439f327756317ea15a32983cfd29503add8a6ff9716b92e50c03dfd7b`; raw table `c24d6b9c8a9456505fa7a5b7c42b85468e6dd76bd49af54d17696c16dec4d2e8`.

Commands/results: read-only `git rev-parse HEAD`/status; `sha256sum` exact inputs; bounded `rg` enumeration of Local writes, graph replacements, callers, unsafe constructs, allocator configuration and collection layout; bounded `sed` of all relevant constructors/inverse owners; note diff/whitespace inspection. Missing unsafe/custom allocator matches returned rg status 1, not an execution failure. Repository-wide allocator configuration and whole compiler semantics were not exhaustively searched. Only this leased note was written; one leaf, short shell reads/hashes, zero heavyweight processes/performance samples. CPU/RSS were not measured; work remained within the 30-minute ceiling. Effective runtime model metadata unknown.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-retained-parent-rollback-falsifier.md`.
- Baseline SHA: `146025ddcafeeae412d9a8b8da5dda536d30f250`, pinned worktree hashes above.
- Dependency change detected, none authored: `lib.rs` initial `c0d8a21567cad455e41e644501bc06406c37efb1aef60792451161cd3546af50` → revalidated `effd339a610e9c33185ba16c206bbba094ce372214fe11ceb5baaa0175e77a9b`; other directly rehashed packet inputs unchanged. Primary identifies the delta as unrelated cfg(test) workspace-growth trace instrumentation; targeted source regions were reread unchanged.
- Review status: producer-only, unreviewed bounded characterization/conditional derivation; parent OPEN; no self-certification.
- Checks already run: exact hashes, write/caller and inverse-order searches, narrow source/library reads, leased-note scope/whitespace inspection; no executable verification.
- Proposed checkpoint message: `Record retained rollback owner and byte-sum falsification audit`.
- Shared-record deltas intentionally left to primary/curator: correct failure ordering (F/receipt inverse precedes targeted checks); record concrete Local ownership exclusion and explicit runtime allocation premise for refresh; preserve all remaining W/semantic/lifecycle gates and exact dependency-delta status. No shared records edited.

Artifact freezes after final leased-note checks; no further writes for frozen review.
