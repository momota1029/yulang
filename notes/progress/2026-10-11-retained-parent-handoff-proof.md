# Retained provenance-child completion barrier: bounded derivation

Date: 2026-10-11
Status: producer-only, unreviewed conditional state-machine derivation. This is not an established Rust correspondence or closure of the original parent theorem.
Producer: leaf `/root/retained_parent_handoff_proof`; no delegation or certification authority.
Exclusive output lease: this note only.
Baseline: `b5aa9189ea705a78d36aba648513bc7a40e1a548`, branch `research/simple-sub-intrusion`; underlying retained-owner code gate `21a1e672f`.

## Objective, dependencies and corrected statement

Supply the missing retained child-to-replay/restoration/Local handoff lemma in [the parent composition](2026-10-11-nonterminal-drain-owner-composition-proof.md), sections “Frozen objects, statement and exclusions”, “Hypotheses: separate owner bridge from supplied local laws”, and “Actual source anchors and missing operational bridge”. [The current source bridge](2026-10-11-nonterminal-drain-owner-source-bridge.md), sections “Completion-distinct parent handoff: actual evidence and remaining seam” and “Disposition of W/H2/H4 and original obligation”, identifies its exact missing operational premise and separates the synchronous candidate adapter from the private retained owner.

Authority is the user-approved [private candidate suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md) §3 (innermost ownership and completion before parent advancement), §4 (saved count and live canonical indexed lookup), and §6 (one transaction, exact failure rollback and reserve/account before mutation). The accepted approval is “承認して実装を進めて”. The index is a locator. No new semantic authority is claimed.

The primary supplied the `/root/retained_child_parent_seam` proposal as text: one waiting slot per active replay, `Idle`, `Running { ack, drain_index }`, and `Ready { ack, completion }`, with an exact `ReplayChildAck` destination in the originating typed child. It is a proposed machine, not baseline source truth. The primary then explicitly corrected the initial packet: baseline terminal acknowledgements consume the child **before** ReturnReady creates `DrainCompletion`; Ready is a post-consumption barrier. Delivery checks `consumed == ack.index + 1`, releases that barrier once, and does not consume the acknowledgement again. This note freezes that corrected machine before deriving it.

The literal initial requirement “only receipt delivery permits replay consumption” is false for the baseline-compatible machine; the smallest countertrace appears below. The corrected conclusion gates **parent advancement** on delivery while preserving the existing terminal consumption rule. This explicit correction does not silently weaken or discharge the original parent theorem: its own conclusion already permits acknowledgements after child computation/diagnostics and requires a complete child handoff before parent advancement. The parent remains **OPEN** pending actual source correspondence and fresh independent review.

## Frozen objects, quantifiers and scope

Fix the original Local frame L, captured graph G, already constructed fresh use/remaps U, and its bound cursor `b = next_bound`. Fix the already accepted restoration B with emission e, raw owner/bound endpoints, original opposite count m, cursor `n = next_opposite`, original occurrence/cause and active replay R if present. Fix R's generated ordered relation vector H of length k, frozen fiber heads/prior/product order, queued cursor q and consumed cursor c. Original relation, fiber, context, attachment, provider, witness and residual identities retain their original meanings. An equal relation value at different child positions does not identify those positions.

For the selected child let `a = (R, i)` be its exact operation/index pair, j its originating typed-drain index and F that retained frame. Its exact initial typed task/relation/provenance and previous processing scopes are retained. F owns the original ordered acknowledgement occurrences A, their completed/prepared cursors d/p, its current item, stage, Function pending item and transition count. Q is any finite retained ordered worklist; D is the source bridge's atomic-diagnostic checkpoint projection; P contains both processing scopes. Route entry checkpoint C includes the slot, F and its destination, R/B/L state, Q/D/P and all named semantic undo owners. No new runtime history field is introduced by the proof.

Quantify over every such valid initial state, every finite Q/A with `0 <= d <= p <= |A|`, every finite H, and every finite execution of the proposed transitions under assumptions below. A trace may start partway through Running or Ready; it need not start at a fresh empty-worklist call. Each valid committed Running step returning `DrainStep::More` preserves n, b and the exact child owner/destination. ReturnReady completion and Ready publication also preserve n and b. Only successful delivery of the matching committed Ready receipt releases that child's parent barrier. A nonempty batch permits restoration advancement only after all its child barriers have been delivered in order; Local advancement follows restoration completion. Every failed route within the rollback-success envelope restores the exact checkpointed stage, cursors, slot/receipt and named workspace state.

“More” in this statement is the originating **typed-child step** result. A later parent scheduler step can advance a completed restoration and still report that additional outer work remains; calling such an outer return More would not make it a child-step preservation claim.

This is finite-trace safety and conditional ordering. It does not prove termination, scheduling fairness, unchanged-wait liveness, or uninterrupted/resumed event equivalence under arbitrary external mutations. Atomic Dispatch/extrusion/Diagnostics helpers are the same bounded stage domain as the source bridge. Source/SCC suspension, incidence deferral, lifecycle withdrawal/recomputation/publication, authentic contract §7 evidence, complete Call meaning, effect hygiene, soundness, principality, production certificates and F5 cutover remain separate. No new source restriction, mandatory annotation or inference rule is introduced.

## Separate assumptions and transition laws

**A1 — Lawful ordered acknowledgements.** Import H2's conditional preparation law and H3's acknowledgement-order/ownership law from the parent; do not re-prove them. The designated `a` occurs once in its F's lawful completion sequence. Projection to each operation uses successive exact indices; no other owner consumes R's current child. All F-owned descendant computation and diagnostics precede its acknowledgements. Equal operation IDs may recur with different child indices, and other acknowledgement occurrences retain their own positions. Preparation is not consumption.

**A2 — Atomic stage primitives.** Import the source bridge's bounded H4 stage law: one exposed step is atomic with respect to commit, or an already retained exact subcontinuation owns its unfinished work. F resumes at its saved stage, never through fresh initialization. Direct Function steps receive the saved current processing scope. ReturnReady removes exactly F, restores its saved caller P and returns its completion. The semantic correctness of transport, contexts, Dispatch, extrusion and diagnostics is shared rather than established here.

**A3 — Successful rollback envelope.** Import W's named whole-route workspace/semantic rollback premise, with the source bridge's explicit qualification that outer cursor validation, retained-byte arithmetic and accounting reconciliation succeed. Undo for slot/destination/receipt, F removal, consumed/retired state, restoration and Local cursor changes is reserved before mutation; referenced operations remain alive through reverse restoration. Failed setup changes no covered execution state. No claim of rollback outside this envelope, allocator-address equality, identical HashMap buckets, reduced spare capacity or restored historical resource peaks follows.

**A4 — No nested resume transaction.** Each proposed transition runs in one outer `RetainedResume` transaction. An active Local route calls internal owner primitives; it cannot start another resume transaction. L is present in its owning vector when its route checkpoint is taken, and any temporary pop is reversed before error/pause propagation. There is no hidden commit between terminal consumption, frame removal, slot publication or parent updates. Ordinary synchronous nested helper calls are allowed within their atomic owner; this is an execution-owner condition, not a ban on source recursion.

**A5 — Receipt construction and retention.** Running records `a,j`, and F records the same destination. Only the result of stepping that matching topmost F can construct `Ready { a, completion }`; successful commit makes that receipt eligible for later delivery. `DrainCompletion.transitions` alone is not identity evidence. The binding is supplied by the exact slot/destination and legal construction control edge. Ready does not need an invented second drain-index field because it can arise only from that bound Running transition. A copied completion value conveys no independent authority to advance a parent. Commit reclamation retains every replay referenced by Running/Ready, active restoration or undo.

The proposal's required control laws, **not claims about inspected Rust**, are:

| Transition | Preconditions and retained result |
| --- | --- |
| Select/start | Slot Idle, `c=q=i<k`; select H[i] with exact a. Start F once using the existing owner-idle fresh-start precondition, transfer child to q=i+1, and store Running(a,j)/F destination before any exposed pause. n/b stay fixed. Running-entry Q may thereafter be any finite retained Q; the fresh-start precondition does not restrict the original already-running theorem domain. |
| Running/More | Step the matching F once. Retain Running(a,j), exact F/Q/D/P and all unfinished work. Ordinary terminal acknowledgement may change c from i to i+1 and set retired when final; n/b stay fixed. |
| Running/Complete | Matching ReturnReady removes F and produces its completion. Store Ready(a,completion) in the same transaction; q=c=i+1, n/b unchanged. Deliver is a later route, so no uncommitted receipt escapes to a parent. |
| Ready/deliver | Validate the stored a, its replay, legal receipt binding and `c=q=i+1`; release Ready to Idle once. Do not call child completion or increment c again. If i+1<k the next child can subsequently be selected. If i+1=k the batch now satisfies the parent completion gate. |
| Empty replay | Idle with k=0 and q=c=0 has explicit no-child batch completion. No F or fabricated drain receipt is created. |
| Restoration advance | Require batch completion **and no Running/Ready slot**. Journal, clear its active replay and increment n once. This cannot run merely because c=k or retired=true. |
| Restoration/Local finish | At n=m with no unfinished replay, retire B and return its retained emission e. Only that successful return lets L clear its restoration pointer and increment b once. No fresh use or accepted bound is recreated. |

Waiting-slot handling precedes all `retired`, `consumed==len`, next-child and reclamation shortcuts. This ordering is necessary; the table is not a permission to assume existing source already uses it. Empty completion, final delivery and restoration/Local updates can compose in one later route only in the causal order shown and under A3/A4. Complete-to-Ready itself cannot also perform parent delivery.

## Invariant and transition induction

For an active replay, use the following invariant. “Delivered prefix” describes preceding trace events for the proof; it adds no production reconstruction relation or stored history.

1. **Idle:** `c=q=t`, and every child before t has had its matching completion receipt delivered. No undelivered child owner is hidden. An active restoration keeps R reachable until its own advancement.
2. **Running(a,j):** `a=(R,i)`, the already delivered prefix ends at i, `q=i+1`, and `c` is i or i+1. Exact F exists above its blocked parents with matching destination; c=i+1 means its lawful outer acknowledgement already completed, but F still owns remaining terminal work/return. n/b remain the saved parent cursors. `retired` may already be true when i+1=k; it does not release the barrier.
3. **Ready(a,receipt):** the same delivered prefix ends at i, `q=c=i+1`, originating F is removed, its descendant work and diagnostics are complete, and its previous P is restored. The stored receipt came from matching F's completion and committed publication. R/slot/B/L own its undelivered return. n/b remain fixed. The completion payload is not inferred from endpoints or transition-count equality.
4. **Transaction/identity:** each mutation has live pre-mutation undo until commit or successful rollback. G/U/e/m and retained source identities persist; a route pause does not reconstruct them. Committed preparation resets p to d and later entry reacquires the imported preparation law. Preparation reset is not semantic completion or receipt delivery.

**Base.** Select/start installs item and Running owner together; retained valid Running/Ready starts are already states of the frozen machine. For an empty batch Idle holds with t=0. Imported valid Q/A and stage hypotheses retain their full finite domains.

**Running step.** By A2 a nonterminal successful operation retains current/substage/pending and advances only its actual operation frontier. Function.next may advance on enqueue, but is not n/b or child semantic completion. Imported A1 preparation/ack laws cover descendants and all ordinary ack occurrences. Before the designated ack, c=i; its exact completion changes c once to i+1 only after child computation/diagnostics. Subsequent More can finish other terminal occurrences or change F's stage to ReturnReady. In every case F remains the same bound owner and neither parent cursor is written. Thus the Running invariant survives More even at c=k/retired=true. A queue transfer or generated replay head cannot substitute for this child stage.

**Completion publication.** The only step producing Complete is matching ReturnReady. A1/A2 imply the designated ack has completed, so q=c=i+1. Removing F restores its saved processing scopes; A5 transfers its return authority to Ready in the same A3 transaction. There is no externally committed intermediate state with F gone and no receipt owner. After successful commit Ready holds and n/b are unchanged. If publication or a later fallible operation fails, rollback restores the route-entry F/stage/destination/slot and consumed state, rather than declaring the removed F complete.

**Delivery.** Ready's construction binding and exact a select this outstanding occurrence. Validation of `c=i+1` confirms the prior terminal consumption; an attempted second `complete_replay_child(a)` would fail the original equality check `consumed==a.index`. Delivery instead clears only this receipt barrier. Re-delivery has no Ready slot and cannot match its precondition; copied numeric payloads cannot supply one. Idle now has delivered prefix i+1. This proves single delivery without requiring completion values to be physically non-Copy or globally distinct. If i+1<k, the next selection uses the next exact position, even when H[i+1]=H[i]. If i+1=k, all children have delivered receipts and the batch is parent-complete. This is induction on the generated ordered suffix, not a conclusion from storage alone.

**Restoration and Local.** The explicit empty case or final delivered child plus Idle supplies batch completion. Restoration's guarded update clears its handle and advances n once. It preserves e and m. At n<m, the next relation uses the live canonical owner/opposite at the saved index; contract §4's separate mutation/incidence premise is still required and has not been proved by this barrier argument. At n=m, retained e is returned without insertion. Only this restoration return clears L's handle/increments b. Zero opposites (m=0) use that same completion return, with no replay or F. The advancement sequence therefore follows matching child delivery, completed replay, completed restoration, then Local; no partial child or committed Ready publication supplies an earlier parent step.

**Failure.** A3 restores C at each failed transition. In Running/More this includes any terminal consumed increment and saved stage. In Complete publication it restores F and the former Running slot. If consumed=i+1 was committed by an earlier More, a later publication failure restores that already-consumed Running checkpoint, **not** i. In Ready delivery failure it restores the exact Ready receipt, consumed/retired, parent handles and cursors, so a supported retry can deliver once. Failure after final delivery/restoration/Local changes in the same route restores all those changes together. Referenced operations cannot be reclaimed before undo reads them. This uses the imported rollback premise; it does not re-prove W or its arithmetic envelope.

Induction over transitions proves the product invariant, and induction over finite committed routes proves the corrected safety statement. Neither induction establishes that source constructors emit these transitions.

## Minimized falsifiers and absent-source boundaries

**Literal receipt-before-consumption falsifier:** k=1, q=1, c=0, Running(a,j), F at Acknowledgements with A=[a], d=0, diagnostics complete. One baseline terminal step calls `complete_replay_child(a)`, sets c=1/retired=true, moves F to ReturnReady, and returns More. Commit leaves no DrainCompletion/Ready receipt yet. Thus “only delivery permits consumption” is false. n/b can still be preserved. This is a legal conditional internal terminal state; no actual retained provenance-child source constructor is claimed at the pinned baseline.

**Retired shortcut falsifier:** continue that trace. If replay tests retired or c=k before its Running slot, it returns batch Complete and restoration increments n while F is still ReturnReady. One child and one More suffice. The same bypass exists at Ready before receipt delivery. Slot-first completion/reclamation guards are required source evidence, not optional strengthening of a mathematical claim.

**Second-ack falsifier:** deliver Ready(a,receipt) by calling `complete_replay_child(a)` when c=i+1. The actual primitive requires c=i, so delivery fails. A consumer that increments without that check would double-consume or overrun the vector. Correct delivery validates/releases the barrier.

**Receipt mismatch falsifier:** two valid Ready slots with equal `transitions` but different a. Selecting a receipt by transition count, relation equality or a reused drain index delivers the wrong return. The exact slot/destination construction must bind a; the payload alone cannot prove origin. No extra field is silently added here.

**Publication-undo falsifier:** let consumed=i+1 be committed in Running, then remove F at ReturnReady and install Ready; inject failure. If undo restores only consumed/cursors and lacks slot/destination/F-removal state, the checkpoint Running F is lost or a stale Ready remains. This isolates the new source premise from the already established workspace inverse owner.

These are discriminating transition/consumer attacks, not executable probes or source programs. This lane makes one constructional proof attempt. The missing source control edge was already localized by the prior composition/bridge; another acknowledgement-prefix induction would leave it untouched. Under the required obligation-economy audit, completion-gated parent advancement and exact rollback are A correctness obligations. Losing the naturally known child-return owner is D reconstruction debt, addressed by retaining a canonical slot/destination at construction. This classification supplies no proof-status change and no permission to weaken ordinary inference.

## Actual baseline ownership and required correspondence

All locators below are from `git show b5aa9189e:<path>` in `crates/yu-solver/src/`; concurrent implementation bytes are not inspected or certified here.

| Owning source | Established bounded fact / missing bridge |
| --- | --- |
| `candidate_context.rs:11–45,47–90` | ReplayChildAck has exact operation/index; F has stages/A/d/p; R has generated H/q/c/retired and restoration owner. Neither waiting slot nor child return destination exists in this baseline. |
| `lib.rs:8106–8109,12101–12139` | DrainCompletion contains only transitions; synchronous adapter starts once and loops to Complete. Its constructor requires idle Q. Equal completion payloads are not identity proofs. |
| `lib.rs:12142–12284,12535–12587` | Shared stage/preparation and private retained-route owner exist. Terminal consumes acknowledgements and returns More before later ReturnReady removal creates Complete/restores P. This is the exact distinction preserved by the correction. |
| `candidate_context.rs:1830–1897` | Transfer increments q; completion requires c==index and may retire on final consumption. These actual primitives do not require Ready delivery. |
| `candidate_context.rs:2952–2992` | Provenance child consumption remains synchronous; replay completion uses retired/absence. The proposed slot must precede those shortcuts and hold the matching return. No retained-child receipt consumer follows merely from the existing bool/Queued result. |
| `candidate_extrusion.rs:661–734` | Bound is inserted once, count saved, later indices re-read canonically. Restoration advances only after synchronous ReplayDriveOutcome::Complete. Missing retained path must block this owner behind Running/Ready. |
| `candidate_scheme.rs:1390–1401,1466–1482`; `lib.rs:9131–9136,9365–9386` | Local temporary-pop restoration and cursor checkpoint exist; b advances after restoration returns Some. A new child transition must preserve this ownership while using a single outer route. |
| `candidate_context.rs:1568–1604,1680–1719,1720–1747` | Existing frame/operation undo and retention protect synchronous state. New slot/destination/receipt fields require actual copying, restoration, charge and reclamation guards at these same owners. Existing snapshots do not cover absent fields. |

Required bridge: show actual constructors bind a/j/F destination and install Running once; actual terminal Complete publishes Ready in the same route; all replay selection/completion/reclamation paths consult the slot first; delivery validates the committed exact a and clears it without another ack; restoration/Local consumers obey the resulting barrier; slot/destination/receipt and removal are journaled, retained, reserved and accounted on every relevant failure/commit path. Production's synchronous wrapper and the private commit-between-step driver both need their actual path inventories. The primary's instruction to integrate the slot into real production replay state is an implementation packet, not evidence that this has occurred.

Inherited acknowledgement laws, primitive semantics, successful rollback arithmetic, current-representative incidence side conditions and original source reachability still need their independent owners. A successful finite test or a checker implementing this transition table would not establish those premises. The parent theorem remains OPEN even if this bounded conditional lemma is independently accepted.

## Frozen dependency hashes, checks and resources

SHA-256 below hashes committed bytes at the pinned baseline, not moving live implementation files.

| Dependency | SHA-256 |
| --- | --- |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Parent composition | `fed59c7525595f3d674aaf7c011362267ae54e0ad5ccae920abaaf60bbcf089a` |
| Current-source bridge note | `5831bf8a1cc1363463aae0ac4d78f50737e92f36274cb1261af58def62facdee` |
| Imported prefix proof | `1419b12825c1f555d918829597de6af88ac35f2191d1deb70bc26f7a4c4cc37b` |
| Prefix source audit | `70616b915b5d10532251e3e442e96fc973102755af2937a5bf26ad236b1896cc` |
| Terminal handoff note | `1f2df0b82beecd62572a1a5d9ae384627403beadcc3dd6e05fbeb148a8d706f8` |
| `lib.rs` | `9a32a53d75892521f28d9cce2955244f99ff5f27fc0a22364e656aedfa540e54` |
| `candidate_context.rs` | `7d758c4177dad59a6c7c3422e68955905db12441b06816f4206bac9960fba416` |
| `candidate_extrusion.rs` | `1fcfd729cc1a2afb080efc6ceeb424146bead7aba0142313b3a12d4ee120fade` |
| `candidate_scheme.rs` | `ad3208eea2b348f1e87f1c6958b1d13b2d625ba38a42f5eac22959edd371a825` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |

Checks: read yulang-proofs skill, role registration/pins, required rules, authoritative sections and frozen original notes; read-only `git rev-parse b5aa9189e`, bounded `git show ... | sed/rg` source-owner reads, `python3`/hashlib hashes of twelve exact committed dependencies, and leased-note structural/whitespace/hash inspection. The first broad multi-file read exceeded capture and was replaced by bounded separate reads. No tests, build, Cargo, formatter, executable protocol probe, performance sample, Git mutation, code/test edit, nested CLI or child job ran.

One leaf; short read/hash processes only, no sustained compute workload. Work is within the 30-minute static ceiling; CPU/RSS were not measured. The primary retains verification, independent review and integration ownership. Requested routing: normal prover, `gpt-6.1-sol` / high. `.codex/config.toml` registers prover with Sol/high defaults; its role file omits model/effort pins. This leaf lacks effective runtime metadata: observed model/effort **unknown**. No Astra, reload or override-success claim is made.

One next action: primary obtains the exact completed-source correspondence for the seven transition/retention obligations above and assigns a fresh compiler-referee to the frozen proof/source pair; keep the original parent theorem OPEN until inherited premises and that bridge are established.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-retained-parent-handoff-proof.md`.
- Baseline: `b5aa9189ea705a78d36aba648513bc7a40e1a548`.
- Changed dependency hashes: none authored; the twelve frozen committed hashes above identify inputs. Concurrent implementation changes require a separate source bridge, not reinterpretation of these hashes as current HEAD evidence.
- Claim/review status: unreviewed conditional corrected-machine derivation and minimized falsifiers; parent OPEN; no independent certification or theorem promotion.
- Checks already run: pinned source/authority/owner reads, dependency hashes and leased-note structural/whitespace inspection; no executable verification.
- Proposed research-checkpoint message: `Record conditional retained child completion barrier proof`.
- Shared-record deltas left to primary/curator: record the explicit terminal-consumption versus receipt-delivery correction; retain exact committed receipt delivery, slot-first completion/reclamation and atomic slot/F undo as source obligations; preserve original parent, inherited rollback/incidence and lifecycle/production gates OPEN. No task/index/theory/authority/shared record changed.

Artifact frozen after the final leased-note checks. No further writes are planned.
