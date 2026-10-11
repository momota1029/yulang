# Retained W/A3 rollback: semantic and late-ledger falsification

Date: 2026-10-11
Status: unreviewed bounded source characterization; original W/A3 OPEN. No constructor-qualified counterexample or theorem closure.
Producer: leaf `/root/retained_w_a3_rollback_falsifier`; no delegation, compiler edits or Git authority.
Lease: this note only. Method: static mutation/inverse tracing and discriminating failure-hook inspection; 30-minute ceiling.
Pinned baseline: `e7733686fa3b8c67fa58fbff16bf9e2d46b2d886`, branch `research/simple-sub-intrusion`.

## Objective and exact authority

Attack the remaining **semantic inverse coverage/normal return** and **late bound-ledger return-success** premises in the original retained parent W/A3 obligation. Seek either an actual constructor-qualified semantic mutation that escapes rollback or a real accounting history that makes rollback return an error after workspace reversal. This complements the constructive prover. The earlier Local-presence/GraphState-refresh attack is read as prior evidence and is not repeated.

Governing authority: user-approved [private candidate suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md) §3 (innermost ownership and child completion), §4 (saved-count/live canonical incidence), §6 (one transaction, exact failure rollback, reserve/account before mutation). Accepted approval: “承認して実装を進めて”. Preserve the original quantifiers and named checkpoint state in [nonterminal owner composition](2026-10-11-nonterminal-drain-owner-composition-proof.md), “Frozen objects, statement and exclusions” and H1/W; and [handoff derivation](2026-10-11-retained-parent-handoff-proof.md), A3/A4. The recorded [rollback proof](2026-10-11-retained-parent-rollback-premise-proof.md), “Remaining rollback and original-parent premises”, identifies the remaining semantic and late-ledger premises; its conclusion is not assumed by this falsification.

**Result:** no constructor-qualified semantic escape or late-ledger error witness found within the inspected closed retained Local/replay/typed-drain cone. A one-reserve **corrupted-ledger** witness already exists in the tests. It discriminates rollback-error handling, but its manually assigned `usize::MAX` byte count is not source-constructor evidence. The precise unresolved seam is an allocation that grows a surviving row **before checked accounting rejects it**, plus the representability of cumulative history counters. Successful earlier preflight alone does not exclude that seam.

## Exact forward and inverse order

The closed retained Local helper (`candidate_scheme.rs:1459–1501`) requires one unfinished Local, rejects an active route, and owns `RetainedResume`. It keeps Local in its vector during child execution/delivery; its fallback atomic step restores the temporarily popped frame before propagating failure. The ordinary Local route (`1358–1407`) enables incoming accounting for its synchronous call and resets it on return. The retained helper does not enable that flag; consequently the normal parsed retained continuation exercises rollback's **nonincoming** counter branch. Do not transfer evidence from an incoming Fresh test to that branch without stating the difference.

The mutation/inverse sequence at this baseline is:

| Forward owner | Relevant inverse and failure boundary |
| --- | --- |
| Route entry, `lib.rs:8981–9195` | Snapshots store, intrusion/effect/context checkpoint, source and Local cursor, route lengths, row frontiers, memos/errors/counters. Old-row snapshots are admitted once per row generation. Setup failures reverse the already-started store route. |
| Retained F preparation, queue transfer, stages | Frame preparation retains the old F before mutation; queue push/pop has workspace undo before transfer. Context creations use checkpoint frontiers/logs. Function port admission retains `pending` before enqueue. The exact semantic implementation of each stage still requires its own coverage argument. |
| Ordinary bounds, `candidate_extrusion.rs:411–581` | `journal_value_row` / `journal_effect_row` precedes nested reserve and logical insertion. Reserve may grow capacity, then accounting runs, then the bound is pushed and flags changed. Reversal truncates four lanes and restores flags, metadata, levels and extrusion marks; newly born rows are subsequently removed. |
| Existing memo mutation | `journal_candidate_memo` stores entry memos once, excluding pairs created by this route. Completion and diagnostic-edge writes call it. Intrusion rollback restores these memos before outer rollback removes newly admitted pair keys. This ordering avoids deleting a restored old memo in the inspected admission paths. |
| Terminal ack/Ready/delivery | F update and replay-return snapshots precede Ready publication and pop; delivery snapshots precede clearing Ready. Restoration snapshot precedes child stepping/parent advance. Local cursor is part of the outer checkpoint. |
| Failure, `lib.rs:9235–9237,9339–9700` | Takes journal; store rollback; intrusion → effect → context rollback; source/Local/publication census; ordinary rows; new pair/error keys and error/use suffixes; reset byte/counter baseline; reconcile bound capacities/history; restore physical peaks; Q/D reversal; scratch cleanup; spare journal installation; finally return `accounting_error`. |

Within context rollback (`candidate_context.rs:1581–1680`), order is support validity/registrations, old F snapshots in reverse then new-F truncation, restoration snapshots, replay snapshots, new-operation removal, evidence and other creation/log frontiers, lifecycle generation, bound heads/origins/use/processing, then relation edges. Undo needing an operation executes before that operation's creation-frontier removal. Context/effect processing scopes precede workspace reversal through their checkpoints. The sampled Ready/current/F/ack state is therefore not still unreversed merely because late arithmetic returns Err.

Late error accumulation starts at `lib.rs:9528`. Each reconciliation error replaces `accounting_error`; there is no `?` at those sites. Retained Q/D reversal is at `9666–9671`, and `9700` returns the accumulated error. `finish_route_transaction` uses `rollback_route_transaction()?`, so this error can replace the original operation error. This ordering is source-established; it is not proof that all inverses return normally or restore every semantic field.

## Smallest discriminating witness already present

`tests::f5c_incoming_nested_preflight_overflow_rolls_back_fresh_and_existing_rows` (`lib.rs:30012–30065`) does the following:

1. Constructs a real parsed batch/session and, in its existing-row arm, a real value row.
2. **Directly assigns `session.bound_payload_bytes = usize::MAX`.**
3. Starts a Fresh route; journals that existing row; grows its empty direct-upper allocation once.
4. Enables incoming accounting and calls `record_incoming_bound_capacity_growth` with the real old/current capacities.
5. Forward preflight fails. It explicitly expects `rollback_route_transaction()` to return Err for the existing row, and Ok for a row born inside the route.

The difference is exactly survivor reconciliation: rollback drops a new row, while the old row's new capacity survives and its positive delta is added to the saved MAX ledger. One pre-existing row, one capacity increase and one failed preflight suffice. No logical bound push is required.

This is a static reconstruction of the existing test, **not a newly executed test result**. It uses Fresh, not RetainedResume; it contains no retained Q/D checkpoint or Ready receipt. Its expected error independently confirms the source author's intended failure path, but is neither an independent semantic oracle nor a constructor-valid W/A3 refutation. Assigning the MAX ledger abandons the ordinary equality between that ledger and actual nested capacity charges.

The adjacent mixed-growth test (`30071–30143`) uses `inject_next_incoming_bound_preflight_overflow` to substitute MAX **only in forward preflight**, leaving the true ledger intact. It expects rollback success and reconciles all three growth events. This is the useful discrimination: the test-local rejection hook does not imply that the saved constructor ledger is corrupt. More cases of that same substitution cannot prove natural ledger/history headroom.

## Precise blocked countertrace and arithmetic premises

Let M = `usize::MAX`, P be the entry nested-capacity byte charge, G/R the entry growth/rebuild counters, E the attempt's recorded capacity-change events, K the count of changed surviving row lanes, and T its successfully recorded pre-existing-row growth events. All quantities are mathematical integers here; no machine overflow is silently identified with arithmetic addition.

After resetting P/G/R to the checkpoint, rollback adds each surviving lane's `(current_capacity − saved_capacity) * slot_size` through `record_bound_capacity_growth`. This requires nondecreasing capacity, representable delta and total charge, and headroom for each counter increment. Incoming mode later requires `G + E <= M` and `R + E <= M`; nonincoming mode adds `max(T − K, 0)` after reconciliation. When all surviving events were successfully accounted forward and capacities are monotone, K is at most T and the resulting counters reproduce entry plus T. That is a **conditional arithmetic explanation**, not a theorem that every failed forward event was successfully accounted.

The controlling attack is one existing empty lane whose reserve grows capacity while G=M (or R=M). `record_incoming_bound_capacity_growth` increments the journal's `incoming_bound_growth_events` **before** its counter/byte preflight (`14185–14210,14241–14266`). The preflight returns Err before `record_bound_capacity_growth` can record the event in G/R/T. Rollback still sees a changed surviving capacity; its reconciliation needs `M + 1` and records a late error. With incoming mode false this already fails inside survivor reconciliation; with incoming mode true the later `G+E` check fails too. The logical row length, F and Q may all reverse correctly while the outer return is Err.

This is a minimized **candidate state/trace**, not a constructor-qualified counterexample. No natural source history reaching that G/R boundary was established, and no artificial counter assignment or reduced-word-size model is presented as source evidence. Conversely, live-allocation representability alone cannot bound G/R: the existing fresh-row-drop test (`30198–30238`) preserves growth events after dropping their storage. History counts are not live capacity. Route admission's `u32::MAX` row-generation check (`8987–8993`) is a real finite guard, but this packet does not establish a per-route event bound strong enough to imply 64-bit cumulative headroom, nor analyze every supported architecture.

Thus the exact blocker is: **establish the constructor/history invariant that bounds P, G/R and failed reserve events at this owner, including capacity growth that survives a rejected forward accounting preflight.** Prior GraphState census equality, success of an earlier sample, or successful earlier accounting checks are insufficient for that different ledger. This is an A correctness premise if W requires rollback to return Ok; it remains with the ledger owner. No supported source-domain restriction or new semantic meaning is proposed.

## Hooks, source reachability and semantic attack coverage

Available hooks at `lib.rs:117–196` distinguish pre-reserve rejection from post-reserve rejection for a named F5b capacity lane. Pre-reserve failure mutates no target capacity. Post-reserve injection returns Err after real successful reservation, allowing the target capacity to change. Candidate bound insertion calls that same wrapper before checked accounting and before logical bound insertion; this is the concrete seam to exercise for a source-created retained Local frame. The injected result is test-only evidence about rollback coverage, not a claim that allocator failure naturally grows the vector.

Other inspected hooks: `inject_next_incoming_bound_preflight_overflow` substitutes a forward arithmetic operand; `inject_next_incoming_nested_preflight_abort` fails after growth accounting/sample; context `fail_replay_completion_undo_reserve` and `fail_replay_completion_after` reject preparation before completion; the retained Local `fail_after` injects failure after an actual owner step. Existing parsed retained tests (`candidate_context_tests.rs:4934–5064`) exercise whole-step failures and Ready rollback, but do not force late-ledger overflow. No test was added or run.

The semantic audit inspected old-row metadata/marks, memo admission/replacement and diagnostics, bound evidence/frontiers, restoration/replay/F snapshots, processing scopes, and workspace event reversal. No omitted journal entry was found in those inspected writes. This is a bounded negative finding, not exhaustive proof of every effect/context/store method, nor a proof that reverse HashMap insertion or assertions are valid on all histories. SCC `active_roots/active_uses` mutation belongs to the enclosing graph-plan owner (`candidate_scheme.rs:868–915`), outside the retained child call cone inspected here; its broader source/SCC lifecycle obligations are not imported as a child rollback theorem.

Two excluded tempting attacks were checked to avoid misleading witnesses: arbitrary direct test-closure state mutation is not a constructor transition; synthetic source-support identity allocation is test-only and belongs to the separate lifecycle owner, not the closed retained child constructors. Neither is used to refute this gate.

## Evidence independence, limits and next action

This packet uses actual source constructors/inverse owners and existing test bodies, rather than a checker supplied with assumed transition rules. The source is both implementation under attack and evidence of operational ordering; there is no independent executable semantic oracle. Test expectations are a second artifact encoding intended arithmetic/failure behavior, with the same bookkeeping assumptions. Shared premises: valid Rust collections, correct branch-owned terms/IDs, journal identity/frontier consistency and normal return of inspected ordinary collection operations. Omitted: panics/corruption, allocator/stdlib verification, exhaustive semantic-method coverage, all scheduler states, incidence interference, authentic §7 lifecycle/withdrawal/recomputation, production certificates, Call/hygiene/soundness/principality and F5 cutover.

No seeds/ranges, models, mutations, bounded enumeration, Cargo processes, builds, test runs, broad suites or performance samples were executed. Static reads used bounded `rg`/`sed`, Git read-only revision/diff/hash queries, and exact hashes. Initial combined tool capture truncated some broad output; relevant contract/original statement and operational source regions were reread in smaller captures. CPU/RSS were not measured; short shell processes only. Work stopped inside the 30-minute ceiling; observed model/effort metadata unknown.

Recommended next action: have the ledger owner establish constructor/history headroom **including failed preflight growth on surviving rows**, with a separately authorized focused source-owned post-reserve failure regression if needed. Apply that result only to late rollback return-success; preserve semantic inverse coverage and original W/A3 OPEN until their own evidence is independently reviewed. Another toy MAX-counter probe would leave the same source-history premise untouched.

## Frozen dependencies

All compiler hashes below equal the pinned baseline. HEAD advanced during read-only work to `0c7e3b423b65c1decfba0759a0a9eec281f442c5`; the targeted dependency diff changed only the original composition note by an 18-line native-H3 sublemma. This packet uses the baseline's original quantifiers and W premise; it neither relies on that addition nor certifies it. The composition baseline hash is used below. Unrelated untracked architecture work was preserved.

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `7ace990203b77f1b8aad185e8cdbb2cdac90b967e38479774b7081e45c9429ee` |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `candidate_context_tests.rs` | `5589562bfa4de07f8324f61a98c04cbebc898c28bfc2796a1f81a84d985aca39` |
| `candidate_extrusion.rs` | `a76979f01feaf76ffa351625b0443802fca3e6e2b0288b55e274d7538ae22ead` |
| `candidate_scheme.rs` | `b15d72a5be0f82b2dba37b12fdc3e11a555253ff92ae7aa615b05aaa00380768` |
| `candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Original composition at baseline | `fed59c7525595f3d674aaf7c011362267ae54e0ad5ccae920abaaf60bbcf089a` |
| Handoff derivation | `052ac8e6499b116f4ec7adc8e9c935ee04f02c8a27419428a4659514a7c12357` |
| Handoff source bridge | `538ccff23338c0c55cdc6bc4cda535b50f55644e342d9fe925ae8c63dcc0a44d` |
| Recorded rollback proof | `2d526b7df88acedd18c306e6ae5bad15314eed6451d4dd87eddc53c74711cdf7` |
| Earlier falsifier | `f9dda14a91a55ef0cd477e5e66bd38de78171fcffcf337bdc01c8b7932b7391a` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-retained-parent-wa3-rollback-falsifier.md`.
- Baseline SHA: `e7733686fa3b8c67fa58fbff16bf9e2d46b2d886`.
- Changed dependency hashes: no compiler/authority/rollback-bridge dependency changed or was authored by this leaf. Concurrent original-composition note `fed59c7525595f3d674aaf7c011362267ae54e0ad5ccae920abaaf60bbcf089a` → `4344694f4b8a8c4a225aae83d3c39fcf242f92c2ff32f0ae059d84ad85ff9222`; baseline W/quantifiers unchanged and used here.
- Claim/review status: producer-only unreviewed bounded negative source finding plus corrupted-ledger witness and explicit candidate countertrace; no constructor-qualified refutation, independent review or theorem closure.
- Checks run: exact dependency hashes and pinned/live compiler comparison; targeted constructor/mutation/inverse/hook/test-body reads; leased-note scope and whitespace inspection. No executable verification.
- Proposed one-line checkpoint message: `Record retained W/A3 semantic and late-ledger falsification seams`.
- Shared-record deltas intentionally left to primary/curator: record late errors occur after Q/D reversal; distinguish existing corrupted-ledger Fresh witness from constructor-qualified retained evidence; retain failed-preflight survivor/headroom premise and semantic inverse coverage as OPEN; do not promote W/A3 from this packet. No shared records edited.

Artifact freezes after final dependency and leased-note checks. Stop writes before review.
