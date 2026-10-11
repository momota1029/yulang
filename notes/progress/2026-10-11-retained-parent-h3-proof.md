# Retained parent H3: constructive acknowledgement conservation

Date: 2026-10-11
Status: **unreviewed constructive source derivation for native histories**, with a conditional rollback extension. No parent closure, independent certification, or production authority.
Producer: leaf `/root/retained_h3_constructive_proof`; no delegation.
Exclusive output lease: this note only; 35-minute static-read ceiling.
Baseline locator: branch `research/simple-sub-intrusion`, primary-pinned HEAD `56a8dd529bf530549730a65ccccd06f821d27b3b`; proof source is the separately authorized frozen, uncommitted retained implementation identified by hashes below, rather than that commit's compiler files.

## Objective, authority and exact target

Construct the acknowledgement-lineage component of H3 in [the original composition](2026-10-11-nonterminal-drain-owner-composition-proof.md), “Frozen objects, statement and exclusions” and “Hypotheses: separate owner bridge from supplied local laws”; supply its corresponding A1 component in [the retained handoff derivation](2026-10-11-retained-parent-handoff-proof.md), “Frozen objects, quantifiers and scope” and “Separate assumptions and transition laws”. The method is direct induction over actual replay construction, queue transfer, pop-to-frame transfer, terminal consumption and reclamation, using a conservation equation on existing fields. There is no executable model or new runtime reconstruction layer.

Authority is [the private suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md) §§3/4/5/6, approved with “承認して実装を進めて”, and [contextual attachment admission](../design/2026-10-10-contextual-attachment-admission-design.md) §§4–6. Accepted correction: terminal acknowledgement consumes inside F; Ready delivery releases its subsequent parent-return barrier and never consumes twice. The primary's clarification in this packet treats `last owner` as outstanding completion, active restoration, Running/Ready or rollback ownership: a historical numeric ID in completed A is not by itself an outstanding owner. This clarifies the source reading; it supplies no scheduler or semantic premise.

Original H3 remains:

> All promised replay completion events are owned by this drain or its exact nested child owner. For each operation r, projecting the outstanding completion sequence onto r yields its successive exact indices beginning at the current `consumed_r`; no outside owner consumes one of those children between these events. Later append/transfer obeys the same rule and existing identity checks. Referenced operations, including a retired replay still linked to an active restoration, remain retained until their last owner releases them.

Keep the original binders: L, captured G, constructed fresh-use/remaps U and bound cursor b; accepted B, emission e, raw endpoints, saved opposite count m and cursor n; active R and frozen ordered H; exact a=(R,i), originating F/index j; original A/d/p, finite Q/D, both processing scopes P and checkpoint C. Original source occurrence/cause, relation, fiber, context, attachment, provider, witness and residual identities are unchanged. Equal relations, equal completion payloads and repeated operation IDs at different indices do not identify occurrences.

The parent quantifies over every valid initial state with finite Q/A/H, every valid saved stage and `0 ≤ d ≤ p ≤ |A|`, and every finite trace satisfying its H1–H5. Its conclusions include retained unfinished work, exact failure rollback, completion before parent advancement, and saved-stage resumption. This note does **not** replace that quantifier by freshly initialized states. It derives an H3 lemma for the native construction histories below and identifies the remaining bridge from the parent's whole initial-state/scheduler domain.

## Source snapshot and operational domain

The lawful-owner [source audit](2026-10-11-retained-parent-lawful-owner-source-audit.md), “Native acknowledgement inventory” and “Constructional derivation and descendant ownership”, supplies prior evidence, not a premise that source behavior is correct. Source bodies were read directly. The primary authorized the audited live implementation: `lib.rs` at `7ace9902…` differs from the audit's `effd339a…` only in the separately approved F4 test formula. Current `candidate_context.rs` is `e8c75472…`, differing from the audit's `1b67fa5b…`; the primary reconciled that movement as two scoped dead-code allowances for RetainedInput and its accounting accessor. The inspected H3 code uses the actual Ready drain index already documented in the [handoff source bridge](2026-10-11-retained-parent-handoff-source-bridge.md). No comparison with old committed compiler bytes is claimed.

The native forward domain comprises replay construction and execution by the synchronous candidate source adapter, and its closed `cfg(test)` retained Local helper stepping the same production owners. Atomic calls may take arbitrarily many finite internal operations; there is no assumed interruptibility inside Transport, Context, Dispatch, extrusion or Diagnostics. Arbitrary callback harnesses, arbitrary low-level API calls and additional mutation routes between retained child steps are outside the established source bridge. This is a stated lemma domain, not a restriction of supported source programs or the original parent.

The required source inventory is:

| Owner under `crates/yu-solver/src/` | Actual construction or consumption fact |
| --- | --- |
| `candidate_context.rs:2910–2984` | `candidate_context_begin_replay` allocates a fresh checked operation ID from the shared monotone counter, retains ordered H, and initializes q=c=0/Idle. Relation equality does not merge H positions. Completeness of H's contextual product is a separate semantic claim. |
| `candidate_context.rs:1836–1859,3087–3105`; `lib.rs:12801–12819` | No-provenance selection constructs `(r,q)` from H[q]. `enqueue_item` reserves before transfer; transfer increments q for that new position and then performs infallible **back** insertion. The driver selects the new q on its next iteration. |
| `candidate_context.rs:3010–3033`; `lib.rs:12101–12115` | Provenance Idle requires q=c, selects `(r,c)`, requires idle Q, starts F once, enqueues the initial item, then installs F.destination and Running(a,j) before any successful exposed return. |
| `lib.rs:12186–12216,12742–12747` | The queue consumer pops the front and appends that exact ack to F.A before context execution, endpoint memo omission or equality handling. Reservation/preparation precede the pop. |
| `lib.rs:12218–12247,12324,12519,12610–12627,12790–12798` | Transport changes only the relation field. Dispatch strips the ack from its local copy. Canonical redirects, ordinary task children and Function pending/front work have no ack. F.current's copy retains execution provenance; A owns completion. |
| `lib.rs:12535–12587`; `candidate_context.rs:1911–1919` | The sole non-test `complete_replay_child` caller consumes F.A[d], requires c=ack.index, validates Running's exact a/q when applicable, and increments d only after success. Ready cannot be acknowledged. |
| `candidate_context.rs:1898–1909,3035–3055`; `lib.rs:12589–12596` | Matching Running(a,j), c=q=i+1 binds Ready before F removal. Ready delivery validates a and the saved stack boundary and clears the slot without another consumption. |
| `candidate_context.rs:1680–1739` | Reclamation requires retired/Idle and no unfinished B→R owner. Transactional reclamation occurs only at commit, after undo is no longer needed. Replay owners are visited before restorations are reclaimed. |

Complete bounded searches found exactly two non-test ack constructors: queue-next `(r,q)` and provenance `(r,c)`. `replay_operation_next` and callback-based replay/restore-replay helpers are `cfg(test)` compatibility machinery. Their direct cursor increments are excluded from native execution. Searches also found one production terminal completion caller and no native dispatch re-enqueue of F.current's ack.

The no-provenance caller is `candidate_replay_bound` (`candidate_extrusion.rs:760–802`), reached by Value/Effect application (`805–860`; `lib.rs:11668–11675,13707–13713`), registered-filter execution (`candidate_context.rs:2752–2800`), and qualifying intrusion merge (`candidate_intrusion.rs:603`). These run within the active typed drain's Context/Dispatch or empty-Q intrusion settlement. They create new replay IDs; they do not borrow an existing restoration's replay. Provenance replay belongs to the saved B/R chain (`candidate_extrusion.rs:698–758`) and uses the synchronous loop or closed retained helper (`candidate_scheme.rs:1467–1500`). That helper's no-restoration arm rejects nonempty Q or an active typed drain. No native typed-stage path starts a fresh provenance drain for another existing R.

## Constructive lemma and invariant

**Claim class:** constructive source derivation of structural H3 on every finite native forward history; conditional derivation for histories containing failed routes. Fresh independent review remains required.

For every replay r created on such a history, let k=|H_r|, c=consumed_r, q=queued_r. While r has pending queued children, let F be its native completion owner. Let `π_r` retain only ack occurrences with operation r, keeping their order and exact index. On all exposed states where F is retained:

```
π_r(F.A[F.d..] ++ Q) = [(r,c), (r,c+1), …, (r,q−1)].             (I)
```

The empty interval is empty. Each occurrence on the left has exactly one completion authority in A or Q. F.current and completed A prefixes are not additional completion authorities. The exact pair selects H[index]; any relation equality in H is irrelevant to this identity. The unqueued suffix H[q..k] has no queued completion occurrence yet and remains in the retained replay owner. Provenance selects its next member only after the current Running/Ready barrier is released.

For a no-provenance r, the creating typed F remains the completion owner through its outstanding interval. For provenance r, its one selected a has the matching destination/Running F until ReturnReady; Ready then owns only the return barrier. After that barrier is delivered, the next F may reuse the stack position j with the **next** a. This does not identify the two children. Operations may disappear only with no outstanding interval or parent/return/undo owner.

There is no global claim that q/c increase across rollback, that a numeric pair cannot recur after a canceled generation, or that all generated children terminate. (I) is about the retained history and its present authorities. Failed-route undo may decrease cursors and reuse a canceled ID after restoring the counter; no canceled and retained occurrence coexist.

### Derivation from actual owners

**1. Fresh generation.** Checked allocation and increment make r different from every already retained replay/restoration ID; q=c=0, A/Q contain no native occurrence of this new r, so (I) holds. k may be zero. H is retained as an ordered vector; distinct positions can have the same RelationId. The argument needs no theorem about whether generation emitted every semantically required relation.

**2. Native selection and enqueue.** In the no-provenance path the only new ack is `(r,q)`; transfer increments q and then back insertion appends it after the existing r projection. Thus both sides of (I) append that same position. Preparation and reserve failures before transfer change no authority. A later route error is handled by the separate inverse argument. The low-level API can also accept an already queued index; the native producer does not take that branch to create a second queued occurrence. In provenance Idle, q=c=i and the start enqueues only `(r,i)`, so its interval becomes the singleton. Two subsequent infallible assignments bind a/F/Running before exposure. While Running or Ready the producer cannot select or transfer another child of this r.

**3. Queue to frame.** Front pop and append move the exact occurrence from Q to A. For r equal to the popped operation, the first r occurrence in Q becomes the last r occurrence in A, preserving their concatenation; for every other r the projection is unchanged. No semantic omission intervenes. Acknowledgement-free Function front insertions can delay r but cannot invert its order. No native producer front-inserts an acknowledged item. Repeated H values therefore retain distinct indices and positions. F.current may store the same pair as the appended A occurrence, but the sole consumer reads A[d], and Dispatch clears its local copy before any recursive enqueue. There is no second completion edge from that copy.

**4. Stage work and ownership.** Transport/Context/Dispatch/Function mutate execution and may generate other replay IDs or additional tasks. They do not change r's existing completion authorities except by the selection/pop rules above. The actual no-provenance call graph creates/queues descendants for this F instead of starting another drain of its existing r. Only the topmost F may step. A source action's fresh synchronous entry has no ack; saved B/R uses its matching F. Thus an outside native frame has no occurrence it can supply to the sole terminal completion caller for r. This is established by the construction/caller inventory, rather than inferred from a successful exact-index check.

**5. Terminal consumption.** Acknowledgements begins after the queue is exhausted and the diagnostic stage returns successfully; no subsequent native producer appends acknowledged work during this terminal suffix. If A[d]=a=(r,i), (I) implies i=c_r: it is the first outstanding occurrence of r in A. The actual consumer's equality therefore succeeds on a lawful forward state, advances c once, and then advances d once. Both sides lose their first r occurrence. Other projections are unchanged. This derives lawful order and uniqueness; the primitive's check merely validates the derived index. Preparation only has `c≤i<q` and cannot substitute for this argument. A malformed exact-index failure is not successful consumption.

The native diagnostic reporters (`candidate_effect.rs:558–619`, `lib.rs:13684–13704`) report errors; diagnostic completion (`lib.rs:13062–13425`) writes memo completion and diagnostic scratch, rather than enqueuing replay children. The structural barrier follows their actual control flow. **The semantic correctness of their result, memo omission, contextual discharge, extrusion and replay products is not used to prove (I).** It remains necessary wherever H4/A2 or the full parent claims genuine completion of every required semantic obligation. A helper returning normally is not proof of that semantic conclusion.

**6. Return and reclamation.** When final consumption makes c=k, (I) is empty for r. An ordinary no-provenance r in Idle has no remaining completion authority; it has no B owner and may be reclaimed. Completed A entries may retain its numeric ID. For the designated provenance r, final consumption may set retired while Running still owns F's return; the reclamation check retains it. ReturnReady publishes matching Ready before F removal, so the return authority has no exposed gap. Ready delivery changes neither c nor (I), and cannot happen twice without a new Ready construction. B still retains r until its guarded advancement releases the pointer. At commit, undo ownership is discarded before reclamation; active B/Running/Ready still prevent removal. Nontransactional terminal reclamation is safe by the empty interval and lack of those owners. Physical numeric-ID occurrences in completed A are historical records, not permission for another consumption. The source has no general reference-count mechanism; this last-owner argument applies to the inventoried native owners.

Induction over the actual forward operations proves (I), sole completion ownership, lawful per-r terminal indices, and retention through the final active owner. After each consumption the remaining sequence starts at the new c; later native appends extend it by the next q. Applying those conclusions to H3 discharges its **structural native-history component**. It does not make native construction of a stored constraint proof of complete semantic activation/replay.

## Failures, original scope and the remaining premise

For failure, `candidate_context.rs:1581–1618` restores original pre-route F objects, reverses replay/restoration snapshots, removes route-created operations, and restores the allocation counter. The existing Q inverse (`lib.rs:12750–12785`) reverses pushes/pops in order. If the outer rollback owner reaches these inverses with their retained objects intact and completes them, its acknowledgement projection equals C exactly: (I) and the completion ownership at entry are recovered, even when the failed route had already consumed a child. An exact inverse may erase such transient consumption and allow the restored child to be retried; that is not duplicate committed completion. Commit resets p=d without altering A/d/Q/c/q, so it preserves (I).

This is a **conditional rollback extension**, not a proof that every semantic inverse returns normally, all late accounting succeeds, or every original route reaches workspace reversal. The separately owned rollback premise remains needed. The local fields and reverse order are inspected source facts; a stored snapshot alone would not establish activation of the whole inverse. No full W/A3 inverse theorem is claimed here.

The exact remaining parent premise is:

> Every initial state and resumed execution admitted by the original retained scheduler is either a cut of the native construction above, or comes with an independently established extension of the same occurrence-to-owner conservation law. Any admitted concurrent mutation or invalidation/recomputation route must preserve or explicitly transfer that ownership, retain the exact dependency/source lineage, and restore it on failure before the saved continuation is reused.

Neither successful preparation, terminal equality checks nor the closed one-Local helper establishes this universal source-domain/scheduler admission bridge. The original arbitrary valid Q/A/stage binders remain in the parent; this note has not declared arbitrary manually assembled Q/A lawful, proved every such state source-realizable, or selected a new definition of valid. The implemented source wait owner checks whole action/publication boundaries; it does not authenticate an additional route between retained child steps. The needed lifecycle-aware innermost admission/deferral/recomputation owner is localized in the lawful-owner audit, “Contract §4: exact mutation and scheduling seam”. §4's saved-count/live-index incidence and §5's old-generation observation withdrawal remain separate requirements. No foreign-consumption counterexample inside the native domain was constructed.

Two static API discriminators show why a wider claim would fail without that bridge: an already queued `(r,0)` can be enqueued again by an arbitrary lower-level caller while c=0/q=1; an Idle operation's completion primitive does not inspect its caller's F identity. These are malformed-call possibilities, not source-qualified language counterexamples. The native constructors/caller inventory exclude them. No global source rejection or annotation restriction is proposed to exclude them from ordinary inference.

**Proof-obligation-economy audit.** The earlier proposal induction imported H3; the subsequent source audit established native producer/consumer control flow while leaving scheduler admission open. The present conservation derivation genuinely derives the forward pair-order/authority premise from those constructors, but the full scheduler join is still untouched. Completion ownership/retention is A correctness. Any missing natural resumption/recomputation is also an A/B requirement under the contract, not an optional C characterization. Exact a, destination, A/d, wait slot and B pointer already retain the naturally known lineage; another inverse relation or endpoint-ID reconstruction would add D debt. The next decisive work is the owning lifecycle admission/recomputation construction and its source bridge, rather than another equivalent FIFO proof. Classification changes no gate status or authority.

## Coverage, resources and frozen dependencies

Checks: bounded `cat`/`sed` governing-source and constructor/consumer reads; `rg -n` inventories of ack literals, queue operations, A/c/q/wait writes, completion/start/replay/application callers and diagnostic owners; SHA-256 input checks. Initial read-only `git status --short`/`git rev-parse HEAD` resolved the supplied locator despite the packet's no-Git-command constraint; that was a packet deviation. No Git mutation occurred and no later Git command was used. Oversized initial grouped captures were replaced by bounded decisive reads. No tests, builds, Cargo, executable probes, random search, performance measurements, formatter, other output writes or delegation ran. Primary owns verification and independent review.

One leaf; short lightweight read/hash processes only, within the 35-minute ceiling. Sustained process count and performance sample count: zero. CPU/RSS and effective runtime model/effort are unmeasured. Requested routing is normal prover/Sol-high policy; config registers prover with GPT-6.1 Sol/high defaults and the role omits model/effort pins. The effective observed model/effort is **unknown**. No Astra, hot reload or override success is claimed.

| Exact dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `7ace990203b77f1b8aad185e8cdbb2cdac90b967e38479774b7081e45c9429ee` |
| `crates/yu-solver/src/candidate_context.rs` | `e8c7547260b20c086daca0300611eb5da972b5c56b1cb109491bb32833adf896` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `a76979f01feaf76ffa351625b0443802fca3e6e2b0288b55e274d7538ae22ead` |
| `crates/yu-solver/src/candidate_scheme.rs` | `b15d72a5be0f82b2dba37b12fdc3e11a555253ff92ae7aa615b05aaa00380768` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Contextual attachment admission contract | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| Original parent composition | `fed59c7525595f3d674aaf7c011362267ae54e0ad5ccae920abaaf60bbcf089a` |
| Retained handoff proof | `052ac8e6499b116f4ec7adc8e9c935ee04f02c8a27419428a4659514a7c12357` |
| Retained handoff source bridge | `538ccff23338c0c55cdc6bc4cda535b50f55644e342d9fe925ae8c63dcc0a44d` |
| Lawful-owner source audit | `f362b08cec82dd01a105be26b9152a4cb18fdea9a7715bf6a6f5bce7e38a68f2` |

Unverified: full retained scheduler and all initial-state source coverage; activation/completeness of generated contextual obligations and semantic atomic helpers; complete rollback/late accounting; mutation incidence stability and recomputation dependency coverage; authentic §7 lifecycle, SCC publication, complete Call meaning, effect hygiene, soundness, required principality, production certificates and F5 cutover. No successful source search or finite fixture closes these obligations.

One next action: primary applies this structural lemma to H3's native branch after fresh independent proof review, and assigns the exact remaining lifecycle admission/recomputation conservation bridge to its owning lane; keep the original parent OPEN.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-retained-parent-h3-proof.md`.
- Baseline SHA: `56a8dd529bf530549730a65ccccd06f821d27b3b`; frozen uncommitted proof-source hashes above are authoritative inputs for this artifact.
- Dependency deltas: no input authored by this leaf. Audit `lib.rs` `effd339a…` → authorized `7ace9902…` is test-formula only; audit context `1b67fa5b…` → inspected `e8c75472…` is primary-reconciled dead-code attributes only. These reconciliations are supplied by the primary, not an independent Git diff by this leaf. Full hashes appear above and in the audit.
- Claim/review status: unreviewed constructive structural H3 derivation for native forward histories, conditional failure extension; exact broader source/scheduler premise remains OPEN. No self-certification or theorem/production status promotion.
- Checks already run: static source/caller/mutation inventories, exact input hashes, leased-note text/whitespace/hash checks; no executable verification.
- Proposed checkpoint message: `research: derive native retained replay acknowledgement conservation`.
- Shared-record deltas left to primary/curator: record the native interval/sole-owner derivation; separate its structural conclusion from semantic atomic completion; retain exact inverse and whole source/scheduler admission/recomputation bridge, incidence and all lifecycle/production gates OPEN. No shared task/index/theory/authority record edited.

Artifact frozen after final dependency and leased-note checks; no further writes planned.
