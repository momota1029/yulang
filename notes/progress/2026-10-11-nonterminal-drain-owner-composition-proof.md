# Retained nonterminal typed-drain owner: conditional composition

Date: 2026-10-11
Status: unreviewed research checkpoint; conditional derivation, not an established theorem or Rust implementation correspondence.
Baseline: `2dbd86d0fa7af783d40cb71de522e9c124127b46`, branch `research/simple-sub-intrusion`.
Producer: leaf `/root/nonterminal_owner_proof`.
Exclusive output lease: this note only; static work, 30-minute ceiling.

## Objective, sources and method

Compose the existing acknowledgement-prefix derivation with an explicitly assumed whole-route continuation owner. The method is induction over finite stage transitions and then over committed route slices, with a separate child-to-parent handoff argument. The prefix induction is imported, not repeated.

Authority is the user-approved [private candidate suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md), §3 (innermost-first ownership and completion before parent advancement) and §6 (one route transaction, exact rollback, reservation and accounting before mutation). §4's saved-count/live-index restoration order remains a side condition; this note does not derive incidence stability. The committed [prefix proof](2026-10-11-nonterminal-ack-prefix-proof.md), sections “Frozen statement and hypotheses” and “Invariant with an actual journal meaning”, supplies a conditional premise, with its existing unreviewed status. The committed [source audit](2026-10-11-nonterminal-ack-prefix-source-audit.md), sections “Earliest safe seam and uncovered bypasses” and “Replay operation and undo inventory”, supplies bounded source evidence. The reviewed [terminal foundation](2026-10-11-typed-drain-terminal-handoff.md) supplies the synchronous terminal owner, not a general resume caller.

All semantic/source reads used `git show 2dbd86d0f:<path>`. `tasks/current.md:8782–8796` leaves nonterminal ownership/route rollback open and Dispatch/Function atomic. The index locates the governing contract; it supplies no additional authority. The `yulang-proofs` skill and the required orchestration, laboratory, design-authority, compiler-engineering and Git-concurrency rules were read. This leaf has no coordination exception and launched no jobs.

## Frozen objects, statement and exclusions

Fix an existing Local-use frame L, its captured graph G and already constructed fresh-use/remaps U; an accepted bound-restoration B with its emission b, raw owner/bound endpoints, original opposite count m and next index n; its active replay R if present; and the topmost unfinished typed drain F of that child. Original occurrence/cause, relation, fiber, context, attachment and provider identities remain the retained ones. No endpoint spelling or adjacency reconstructs them.

At route entry fix an ordered saved queue Q of any finite length, the exact current item and stage of F, diagnostic continuation D, both processing scopes P, and route checkpoint C. F has ordered acknowledgements A, completed cursor d and prepared cursor p. Each A[i] is an occurrence at position i holding the exact `(operation, child_index)` pair. Equal operation IDs and equal child relations may recur; they do not identify occurrence positions. For each replay r, its ordered generated vector H_r and cursors satisfy `0 <= consumed_r <= queued_r <= |H_r|`.

For every such finite initial Q and A, every valid stage at the route entry, every `0 <= d <= p <= |A|`, and every finite sequence of routes and resumed stage transitions satisfying H1–H5 below, the following conclusions hold:

1. Until the child drain returns Complete, its unfinished current item, queued work, diagnostic continuation, acknowledgements and processing scopes remain owned by the same route/session continuation. A resumed stage does not recreate U, reinsert b, regenerate the same R, or skip unfinished work.
2. A route failure restores the exact checkpointed continuation and semantic mutation state C, including Q in its original order, D, P, F, replay/restoration cursors and L's cursor. This is exact equality on the named checkpoint state, not equality only of queue length or unordered task sets.
3. Preparation and queue transfer are distinct from semantic child completion. An acknowledgement advances F.d and its replay consumed cursor only after its child computation and diagnostics have completed. A restoration opposite index advances only after the corresponding replay batch's child drains return Complete. L's bound index advances only after its restoration returns Complete.
4. Successful pause commits the unfinished ownership without completing a parent. Subsequent route entry reacquires preparation in its new journal and resumes the retained innermost stage. ReturnReady removal restores the saved caller processing scopes before the child returns Complete.

This is a safety statement over finite traces. A finite saved queue does not imply a finite transitive computation: dispatch may generate further work. There is no assertion of unconditional termination, fair scheduling, prompt unchanged-wait behavior, or equivalence of completed results to an independently specified semantics.

Excluded: actual nonterminal Rust source reachability; general interruptibility inside atomic transport/context/Dispatch/diagnostic helpers; external incidence disjointness; lifecycle certificate validation, withdrawal/recomputation and publication; authentic §7 coverage; source/SCC suspension; complete Call meaning, effect hygiene, soundness, principality, production certificates and F5 cutover. These remain separate obligations. No source restriction, ID-uniqueness rule or new semantic policy follows.

## Hypotheses: separate owner bridge from supplied local laws

**H1 — Whole-route owner lemma W (assumed, not established).** There exists a retained nonterminal route boundary that can start with the above Q, D and P, freezes C before mutation, and owns the exact active stack and child-return destination. For each transition:

- storage and undo for the state about to change are fallibly reserved before mutation; F's original allocation is retained before updating an old F;
- moving an item from Q to F.current, replacing a stage result, installing a pending Function item, or transferring a child return never leaves the only continuation in an unretained local variable at a possible pause/error;
- each primitive stage operation either completes atomically, or retains its own exact internal continuation. The caller records the next stage only after that operation completes; a partial operation cannot masquerade as a completed stage;
- failure reaches one rollback owner which composes the semantic journals with exact Q/D/P and continuation restoration, including old objects temporarily removed from the stack. New objects are removed after any undo needing them. Rollback itself succeeds on the admitted envelope;
- success/pause commits the retained continuation, keeps unfinished parent handles live, and charges all retained/rollback storage. Resources needed by reverse restoration remain owned until that restoration finishes.

W is an independent structural premise about retaining state and closing a transaction. It does not assume lawful acknowledgement order, replay completion, restoration advancement or Local advancement. Those are supplied by H2–H5 and derived below. A checkpoint of only the context's vector lengths is insufficient for W. For §6 accounting beyond this named checkpoint projection, the implementation must also supply its exact retained-allocation/accounting rule; the existing prefix proof makes no promise that undo capacity or historical resource peaks shrink on rollback.

**H2 — Prefix law P (imported conditionally).** At every resumed nonterminal entry, before any saved-stage effect/pop/append or direct Function step, F and A's entire outstanding prefix are prepared against the active route journal by the rule in the committed prefix proof. An already prepared position is not independently reclassified by an operation-ID set. On success p=|A|, with one retained journal event for each prepared occurrence. The existing pre-pop reservation/append law is used for later queue entries. A commit resets p=d and the next nonterminal route reacquires preparation. The terminal-only step retains its existing one-next-ack rule; this theorem does not require a full scan there.

**H3 — Lawful ordered acknowledgements and ownership.** All promised replay completion events are owned by this drain or its exact nested child owner. For each operation r, projecting the outstanding completion sequence onto r yields its successive exact indices beginning at the current `consumed_r`; no outside owner consumes one of those children between these events. Later append/transfer obeys the same rule and existing identity checks. Referenced operations, including a retired replay still linked to an active restoration, remain retained until their last owner releases them. This is not inferred from successful preparation: preparation validates `consumed <= index < queued`, while completion requires `consumed == index`.

**Reviewed native H3 sublemma.** The constructive proof in
[`retained-parent-h3-proof`](2026-10-11-retained-parent-h3-proof.md) establishes,
for successful finite native replay-construction/forward histories, the
per-operation conservation equation
`π_r(A_F[d..] ++ Q) = [(r,c), …, (r,q−1)]`. A fresh compiler-referee found no
correctness issue in that bounded derivation. It establishes one completion
authority per native occurrence, exact FIFO indices, and retention through the
last active completion/restoration/return owner. This discharges H3 for that
native source domain without assuming semantic correctness of the helper
operations.

This sublemma does not discharge the original H3 quantifier over every valid
initial Q/A/H and admitted scheduler state. The remaining bridge must show that
every admitted initial/resumed state is a native construction cut, or prove
that any additional admitted mutation and its ordered invalidation/recomputation
preserve the same equation. Exact rollback remains conditional on the inverse
premise in W. Therefore the original composition and W/A3 remain OPEN.

**H4 — Retained stage protocol.** The resume driver starts at F's retained stage, current item and substage, uses the existing queue selection/enqueue order, and does not execute the fresh constructor's initialization/reset again. It drains all descendants owned by F, completes the exact diagnostic work, and only then enters Acknowledgements. At every child-call boundary an unfinished child has a retained frame above its blocked parent. Function.next denotes port admission/enqueue progress, not child semantic completion. Resuming FunctionEnqueue uses the saved pending item, not a second port admission. Diagnostics are atomic here unless W retains their internal cursor; replaying all diagnostic work after a partial unrecorded completion is outside H4.

**H5 — Parent gate and mutation side conditions.** The driver returns a distinction between Complete and unfinished continuation. Replay generation/queue transfer, a boolean “transferred”, or a successful pause cannot satisfy Complete. Restoration uses the provenance-bearing child-consumption path and advances its next opposite only after all children of its active replay Complete; Local advances its bound cursor only after restoration Complete. Their updates use the existing journal-before-mutation owners. The original saved opposite count is retained, each later opposite index is re-read using current canonical representatives, and interfering external changes are deferred or separately proved harmless under contract §4. Allocation/accounting errors abort before continuing. No hidden commit releases undo mid-route.

H4/H5 are the control protocol being composed, with synchronous source anchors below; the absent resumed caller has not been shown to implement them. W is neither assumed language semantics nor a claim that reading a checkpoint already proves a rollback owner exists.

## Derivation

Use a product invariant with three independent components: (I) all unfinished execution has a retained location in the continuation/Q/D, with exact relation/provenance and parent-return destination; (J) each mutation interval is covered by C and the appropriate live undo, including the prefix law's occurrence-to-journal mapping; (K) semantic completion frontiers change only at the corresponding completed-child gate. G, U, b, m and replay generation identities are retained throughout. These are proof descriptions of the owned fields, not proposed runtime reconstruction relations.

**Route entry.** W obtains the saved innermost frame without resetting it and establishes C. P prepares the outstanding acknowledgement prefix before the first resumed effect. A preparation failure is an error transition back to C; it cannot run dispatch or advance a semantic frontier. This uses the prefix result as a lemma. It adds no proof of that result or its source reachability.

**Queue/current transfer.** For an acknowledged front item, P supplies reservation before pop and occurrence-preserving append. W retains the popped exact item in F.current before any fallible stage runs; for an unacknowledged item the same ownership transfer still applies. The remaining ordered Q is retained by W. The copy of the ack in current preserves item identity; the appended A position holds completion responsibility, so the copy does not authorize a second consumption. `queued` means the generated child reached its queue owner, not that the computation finished. Thus I/J persist and K does not change.

**Transport, Context and Dispatch.** Each operation uses the retained item/relation/processing and is atomic or owns its subcontinuation under W. H4 changes stage only after completion. If it enqueues more tasks, each occurrence enters Q by the original ordered insertion rule; none is discarded because another occurrence has equal endpoints. If the operation pauses internally, its child frame retains the unfinished state and the caller does not change stage. No acknowledgement or parent bound cursor advances. This extends I/J/K by one transition. The argument is conditional for each such primitive; it supplies no new proof of its semantic correctness or undo coverage.

**FunctionAdmission and FunctionEnqueue.** Successful port admission leaves the exact pending item and Enqueue stage owned. Pause there preserves that item. Successful enqueue transfers it to Q, clears pending and increments Function.next once. Failure before enqueue success restores C. This cursor is allowed to advance after enqueue, before child completion: it is an enqueue frontier. The semantic completion frontiers in K remain unchanged until that queued child drains. Treating Function.next as a completed-child count would falsify the statement being proved.

**Diagnostics and acknowledgements.** H4 requires the remaining owned work to finish before the diagnostic barrier, and diagnostic completion before Acknowledgements. W retains exact diagnostic progress; a failure restores its checkpoint rather than silently clearing pre-route scratch. P supplies current-route acknowledgement undo; H3 supplies the exact completion index. The terminal step consumes A[d] and only then increments d. Each occurrence advances its operation's consumed cursor once. A projection such as `(r,0),(s,0),(r,1)` therefore preserves all three events; the relation values may be identical. The malformed repeated pair `(r,0),(r,0)` is not silently removed: the second completion fails its exact-index check and rolls back. It is outside lawful success H3, inside the failure claim.

When d=|A| the drain is ReturnReady. Its next successful removal restores both saved processing scopes and produces Complete. An interrupted ReturnReady still has its frame; it is not permission for a parent to infer completion early. Empty A uses the same diagnostic/return barrier without a replay consumption event.

**Replay → restoration → Local.** A replay with pending child i retains R and exact H_r[i]; nested F is resumed before its replay caller. Until F returns Complete, H5 blocks any parent handoff. On Complete its consumed cursor has advanced after diagnostics; the next child is selected by the exact replay index. By induction on the finite remaining H_r suffix, a completed batch has consumed every remaining occurrence once. Empty batches need no child and use their ordinary journaled retirement path. No generated head or queued count substitutes for this induction.

Only after the active batch completes does restoration clear its replay pointer and increment n once. Its emission b remains the same. If n<m, the next operation re-reads the current canonical owner at original index n, preserving §4 ordering; it does not freeze a new opposite vector or insert b again. At n=m, restoration retires and returns its retained emission. Only this return clears L's restoration pointer and increments L.next_bound once. L retains G/U while any nested operation is unfinished. The zero-opposite case returns restoration completion without creating a replay; the Local cursor still moves only after that return.

**Failure and route composition.** At any failed stage, J remains live until rollback. The imported prefix result restores F/replay fields; the existing restoration undo restores n and the pointer/retired state; the Local cursor checkpoint restores its parent position. W supplies the missing exact Q/D/P and transient-stack restoration and composes all of these with other semantic undo. Consequently the named post-rollback state equals C. Reverse chronological operation snapshots retain every occurrence; deduplication by r would not justify this equality.

At successful pause I holds and no pending child generated Complete. Commit drops this route's undo and resets preparation to completion while retaining the unresolved semantic ownership. At the next entry the same argument applies to the new C and p=d. Induction over any finite number of committed slices proves all four conclusions. It neither turns a pause into `SolveAvailabilityError` nor proves the outward suspension/lifecycle machinery exists.

## Actual source anchors and missing operational bridge

Locators below are at the full pinned baseline in `crates/yu-solver/src/`.

| Actual owner/consumer | Enforced source fact; boundary of evidence |
| --- | --- |
| `candidate_context.rs:20–45,1534–1604,1674–1750` | F retains current/stage/Function progress and ack cursors; frame undo restores an old frame and original ack allocation; commit resets p=d. F does not contain the remaining Q or diagnostic continuation. |
| `candidate_context.rs:1816–1864` | Every transactional preparation appends a replay snapshot; transfer advances queued after reservation; completion checks exact consumed index. No operation-ID deduplication. |
| `lib.rs:11875–11988` | The synchronous creator constructs a new F, requires empty Q, clears diagnostics, initializes work and resets current/Function/stage at its loop header. Its pre-pop reservation protects the new front ack, not an old committed prefix. This is not retained-stage resume. |
| `lib.rs:12227–12341` | Synchronous diagnostics precede Acknowledgements; terminal helper validates topmost terminal stage, prepares before completion, increments d after success, and restores processing after ReturnReady removal. It rejects nonterminal stages. |
| `lib.rs:12351–12373` | Function admission retains pending before enqueue; next increments only after successful enqueue. This source proves an enqueue frontier, not child completion or transactional nonterminal re-entry. |
| `candidate_context.rs:2856–2971` | Generation retains exact ordered children separately from queued/consumed. With provenance, synchronous constrain must finish before child consumption returns. Without provenance, the driver can return `Ok(())` after queue transfer with unconsumed work; that return is not usable as completion in H5. |
| `candidate_extrusion.rs:656–737` | Accepted emission and saved opposite count are retained; restoration journals before update, re-reads the canonical owner at saved n, and advances after the synchronous provenance-bearing replay drive. A future Suspended result must block this advancement explicitly. |
| `candidate_scheme.rs:1361–1402,1466–1484` | Local retains one graph/fresh use, restores its popped frame before each fallible return or test pause, and increments next_bound only after restoration returns Some. Nested typed work currently remains atomic. |
| `lib.rs:9115–9119,9171–9208,9343–9361` | Route entry snapshots source and Local cursor; success commits context undo; error invokes rollback. Local publication allocation/cursor restoration is real, but it is not whole-route W. |
| `lib.rs:8968–8971,9637–9642` | Route begin expects empty Q and diagnostic scratch; rollback clears them. Neither restores a pre-existing nonempty Q or diagnostic continuation. |

**Smallest missing premise:** one callable retained nonterminal route owner satisfying W for an already existing F and its exact Q/D/P, before H2's prefix preflight or any saved-stage side effect, with a completion-distinct return wired to the blocked replay/restoration/Local parent. Supplying this owner must preserve every exposed direct Function seam as well as the main drain entry. Prefix correctness alone cannot supply it.

The smallest queue obstruction requires no replay complexity: let C.Q contain one saved item x and let the next route fail. Clearing the queue yields `[]`, not `[x]`, regardless of perfect replay undo. Similarly one pre-existing diagnostic entry is lost by clearing scratch. These are conditional future-resume countertraces; the baseline empty-entry assertions exclude them from current source reachability. A frame/current item checkpoint alone therefore cannot close W. Independently, returning an unfinished child through the synchronous `Ok(())` parent seam would permit restoration advancement; the source audit must establish the completion-distinct seam, not merely stored frames.

This is one composition attempt, not another attempt to prove W from absent source. W is §6 correctness obligation A. Q/D/P and the child return are already known at their owning drain/route boundaries; reconstructing them after clearing is debt D. The constructional route is to retain their canonical ownership there. No third equivalent prefix proof, ID-set reconstruction, inferred completion from queued progress, or gate reclassification would establish this premise. The audit records the owner and leaves existing gate status unchanged.

## Checks, resource use and frozen dependencies

Checks run: read-only baseline/HEAD resolution; bounded pinned rule/contract/note/source reads and exact owner searches; SHA-256 baseline/live equality checks for the eight dependencies below; leased-note whitespace/lease inspection. No compiler/test edits, tests, build, Cargo, formatter, executable probe, measurement, Git mutation, nested CLI or delegation. One leaf; only short read/hash shell processes. CPU/RSS and reasoning elapsed time were not measured; work remains within the 30-minute static ceiling. Primary remains verification and independent-review owner.

| Dependency | Baseline SHA-256 (live matched when inspected) |
| --- | --- |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Prefix proof | `1419b12825c1f555d918829597de6af88ac35f2191d1deb70bc26f7a4c4cc37b` |
| Prefix source audit | `70616b915b5d10532251e3e442e96fc973102755af2937a5bf26ad236b1896cc` |
| Terminal handoff note | `1f2df0b82beecd62572a1a5d9ae384627403beadcc3dd6e05fbeb148a8d706f8` |
| `candidate_context.rs` | `24909fb9a09e6f9d383e5b1f8f4f8db9d5f7e587a1ed5bbb6a47ead77e140831` |
| `lib.rs` | `77a3c4bdb48d438f7e5678c35302ad2aa1f6665ca9cbb8f3fdc0a48e730a30f4` |
| `candidate_extrusion.rs` | `08e3121924696232bdc75b1eaa3110e2fdc008b948d1c58f6758965b25e0d85d` |
| `candidate_scheme.rs` | `ad3208eea2b348f1e87f1c6958b1d13b2d625ba38a42f5eac22959edd371a825` |

Requested runtime: prover packet, normal `gpt-6.1-sol` / high policy. Callable schema includes prover; configuration registers it with unpinned model/effort and Sol/high defaults. Effective runtime model/effort metadata is unavailable to this leaf and **unknown**; no hot reload, override success or Astra use is claimed.

One next action: primary supplies or leases implementation of W at the actual retained drain/route boundary, then obtains source evidence for its exact Q/D/P checkpoint and completion-distinct parent handoff before applying this composition to Rust.

## Commit packet

- Exact leased/change path: `notes/progress/2026-10-11-nonterminal-drain-owner-composition-proof.md`.
- Baseline: `2dbd86d0fa7af783d40cb71de522e9c124127b46`.
- Changed dependency hashes: none authored; eight baseline/live matches above at inspection. Any later concurrent change requires primary dependency revalidation.
- Claim/review status: producer-only unreviewed conditional composition; imported prefix remains conditional/unreviewed. No established theorem, Rust nonterminal correspondence, gate promotion or self-certification.
- Checks already run: bounded static baseline/source/authority reads, source-owner searches, dependency equality/hash and note whitespace/lease inspection; no executable verification.
- Proposed checkpoint message: `Record conditional retained typed-drain owner composition`.
- Shared-record deltas left for primary/curator: distinguish whole-route W from ack-prefix preparation; preserve exact Q/D/P rollback and completion-distinct parent gate as missing source obligations; retain Dispatch/Function, lifecycle, §7 and production gates open. No shared record or authority file changed.

Artifact frozen for primary review; this leaf will make no further writes after the recorded checks.
