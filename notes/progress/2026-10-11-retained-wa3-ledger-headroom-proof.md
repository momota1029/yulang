# Retained W/A3: the remaining ledger headroom premise

Date: 2026-10-11
Status: independently reviewed bounded conditional derivation with one minor wording repair; the quantified ledger premise and original W/A3 remain **OPEN**. No constructor-qualified refutation or theorem certification.
Producer: leaf `/root/retained_w_a3_rollback_proof`; no delegation.
Exclusive lease: this note only. Baseline: `d99d90ba32471d58cb4c8b9d77ab8266804736fd`, branch `research/simple-sub-intrusion`.

## Objective, authority and frozen statement

The narrow assignment asks whether the actual constructors establish enough cumulative growth/rebuild and surviving-capacity headroom that rollback reconciliation returns normally after a reserve followed by failed accounting. This continues the exact missing premise in [the frozen falsifier](2026-10-11-retained-parent-wa3-rollback-falsifier.md), SHA-256 `093f2d3ef7ea4d3b206939c5dc8475cfbe793e25f3c01682c5b06d4f2afa59ad`. It does not repeat the whole semantic inverse investigation.

Authority is [private candidate suspension](../design/2026-10-11-private-candidate-suspension-contract.md) §6, approved by the user with “承認して実装を進めて”. The original statement is [the nonterminal composition](2026-10-11-nonterminal-drain-owner-composition-proof.md), “Frozen objects, statement and exclusions” and H1/W; its native H3 addition preserves the original quantifiers. [The handoff proof](2026-10-11-retained-parent-handoff-proof.md), A3/A4, and [the reviewed rollback lemma](2026-10-11-retained-parent-rollback-premise-proof.md), “Remaining rollback and original-parent premises”, distinguish the named semantic checkpoint from accounting and rollback-return success. Their independent reviews do not establish the premise investigated here.

Retain the original L/G/U, B/emission/raw endpoints/m/n, R/ordered finite H/q/c, a=(R,i), F/j, finite ordered Q/A with `0 ≤ d ≤ p ≤ |A|`, diagnostic projection D, both processing scopes P and checkpoint C. Original source scopes, binders, occurrence/cause, context, fiber, attachment, provider, witness and residual lineage remain distinct. Histories may begin at any valid retained stage, including committed Running or Ready. The target quantifies over **every constructor-valid retained Local history**, with its actual prior session history, and every failed route within that domain; it is not restricted to histories whose rollback was already successful.

Required conclusion for this packet: the bound ledger reconciliation's checked arithmetic is representable and its final `accounting_error` is absent. W additionally needs all preceding semantic inverses and workspace restoration; those are excluded from this narrow conclusion. No source restriction, practical-size limit, annotation requirement, new inference rule or counter policy is adopted.

## Actual operational bridge

Locators are in `crates/yu-solver/src/` at the pinned baseline.

| Owner | Construction/consumption fact used below |
| --- | --- |
| `lib.rs:88–104,140–181` | `reserve_f5b` for Vec delegates to `try_reserve`; test post-reserve rejection can leave increased physical capacity. No history-counter reservation precedes that allocation in this wrapper. |
| `candidate_extrusion.rs:411–425,459–505,511–581` | Old-row journaling precedes nested reservation. Accounting receives actual old/new capacities **after** reserve; logical push and flag updates follow successful accounting. |
| `lib.rs:9241–9336` | Each pre-existing row is snapshotted once per route generation, including all four entry capacities. A failed snapshot admission cannot reach that row's later reserve through this call. |
| `lib.rs:10139–10204` | Newly created value/effect rows begin with four empty Vec lanes. Rollback truncates these rows, whereas a pre-existing row's increased lane capacity survives. |
| `lib.rs:14185–14288` | A capacity change increments the attempt's `incoming_bound_growth_events` before byte/counter preflight. Successful preflight enters `record_bound_capacity_growth`; a preflight error returns before updating its payload/counters/retained-growth history. |
| `lib.rs:14073–14125` | Each successful changed-capacity recording checks payload, growth and rebuild increments, then records a pre-existing-row event and publishes the computed values. It does not count an event whose earlier checks failed. |
| `lib.rs:9514–9641` | Rollback resets the checkpoint payload/counters, accounts the aggregate capacity delta of each changed surviving lane, then accounts history events. Errors accumulate rather than returning at those sites. |
| `lib.rs:9666–9700` | Retained workspace reversal, scratch cleanup and spare installation precede the final accumulated accounting error return. `finish_route_transaction` at `9235–9237` can therefore return that late error instead of the original operation error. |
| `candidate_scheme.rs:1358–1407,1466–1500` | Synchronous Local routing enables incoming accounting. The closed retained helper does not enable it; the ordinary parsed retained continuation therefore uses the **nonincoming** reconciliation branch. Its checkpoint can nevertheless inherit earlier incoming history counts. |

The claim concerns this real reserve/account/rollback sequence. No model supplied with assumed transitions, arbitrary MAX assignment, or direct test-closure mutation is used as source reachability evidence.

## Derivation of the exact arithmetic obligation

Let M=`usize::MAX`. Read the entry payload as a mathematical integer B and the entry growth/rebuild counts as G/J. Let S be the set of pre-existing lanes that survive this route. For each lane s let its entry/current capacities be x_s/y_s and element size w_s. Let K count the lanes with `y_s != x_s`. Let T be the journal's number of **successfully accounted** growth events on pre-existing rows, and E its recorded attempt capacity-change events, including a recorded event rejected by subsequent preflight.

Forward reservation does not shrink these Vecs; rollback truncates lengths, not capacities. Thus each survivor delta is

```text
Δ_s = (y_s − x_s) w_s ≥ 0.
```

Once-per-row admission prevents double counting a survivor. Summing successive forward capacity increases on a single surviving lane telescopes to this Δ_s, regardless of how many reserves occurred there. New rows contribute zero after removal. Consequently the **intended current nested payload** is exactly

```text
B_after = B + Σ_s Δ_s.
```

This equation comes from the actual owned Vec lanes and saved capacities. It does not treat a growth counter as a live-allocation charge.

If this sum and every increment below fit, induction over the actual reconciliation loop gives payload B_after and counters G+K/J+K. The loop then produces:

```text
incoming:     G_after = G + E,          J_after = J + E;
nonincoming:  G_after = G + max(T,K),   J_after = J + max(T,K).
```

For nonincoming, this follows from adding `T.saturating_sub(K)` after K successful survivor increments. For incoming, the final assignments use the checkpoint counts plus E. Each changed survivor had at least one recorded physical event, except a last event rejected by the attempt-counter increment itself; no branch can assume K≤T after accounting failure. The exact per-prefix checks in the survivor loop are implied by the final inequalities because all increments are nonnegative.

In particular, conditional on the payload/independent lane sums being exact and representable, ordinary reconciliation returns normally if:

```text
incoming:     G+K ≤ M, J+K ≤ M, G+E ≤ M, J+E ≤ M;
nonincoming:  G+max(T,K) ≤ M, J+max(T,K) ≤ M.
```

The separate K checks in incoming mode are retained for the case where the final physical event failed before E was incremented. This characterization describes actual intermediate checks; it does not assume them away. A failed counter increment inside `record_bound_capacity_growth` prevents that call's payload publication too. Thus a late error may also leave an unreconciled payload lane, even though Q/D have already reversed. Normal semantic workspace reversal cannot establish the ledger conclusion.

## What forward checks establish, and the one-event gap

Let f be the number of this route's successful changed-capacity records before its first error. Induction over the actual checked updates establishes `G+f≤M` and `J+f≤M`. Also T≤f. If **every changed survivor** had a successful forward record, K≤T and the nonincoming target follows directly from `G+T≤G+f≤M` and the analogous rebuild inequality. This proves the familiar successful-accounting subcase at its owner.

That subcase does not cover the assigned failure. A capacity-increasing reserve is already complete when accounting starts. If its preflight fails, the caller immediately propagates the error: there can be at most one such final unaccounted physical growth in this route's inspected call sequence. Hence the stronger source-derived bound is only **K≤T+1**, not K≤T. The attempt history similarly can have a final recorded event beyond the successful f records. Post-reserve rejection *after successful accounting* has no such gap and belongs to the successful-record subcase; the two errors must not be conflated.

For the **nonincoming retained-owner branch**, if the final failed growth occurs in a surviving lane that already changed earlier, it adds no new member to K. If prior successful growth on dropped rows gives `f>T`, it can also supply enough counter slack for nonincoming recovery. The undecided case in this branch is a **newly changed surviving lane after all available forward history headroom has been consumed**. Source preflight detects exhaustion after that lane's allocation, and gives no pre-allocation proof that the extra survivor increment needed in rollback fits. This is a missing construction invariant, not evidence that a natural source can reach an exhausted counter.

The **incoming rollback branch** has an additional case: a final failed growth on a row created within the route may be dropped, leaving K unchanged while the recorded attempt count E still increases. Its final `G+E` and `J+E` checks therefore need independent headroom even when no surviving lane changed. The unestablished headroom question is branch-specific: surviving-lane increments for nonincoming recovery; surviving-lane prefixes and all recorded events, including dropped-row events, for incoming recovery.

No toy state with G or B assigned MAX was constructed or promoted. The frozen falsifier's corrupted-ledger test is deliberately not a witness for this theorem.

## Capacity charge and cumulative history are different premises

For bytes, there is a direct conditional derivation. If the entry B is the exact census of these uniquely owned nested Vec buffers, and the execution has valid disjoint addressable Rust collection allocations whose backing bytes cover `capacity*sizeof(T)`, the current survivor sum is representable: it charges a subset of the live nonzero backing bytes. Every nonnegative prefix and every Δ_s then fits. Existing/new row constructors and the once-per-row journal establish the **ownership and telescoping** part. Applicability of that allocator/collection/addressability premise is shared runtime evidence, not checked by this packet. The previous GraphState refresh lemma concerns different immutable buffers and cannot replace it. An induction over failed histories still requires successful reconciliation to preserve the entry census for the next history; it cannot circularly assume all such entries remain exact.

No analogous live-byte argument bounds G/J. Incoming rollback deliberately preserves events from dropped fresh-row allocations (`lib.rs:9610–9623`); the existing fresh-row-drop fixture at `30198–30238` encodes that behavior. This is static test-body evidence of the owner policy, not a newly executed test or an independently specified oracle. Therefore a current allocation census cannot bound the historical event count.

The second attempted route used the actual construction dimensions: route admission refuses exhausted `u32` row-seen generation (`lib.rs:8987–8993`), and new row ordinals are checked `u32` values (`10139–10204`). Those guards bound route/row identities. They do **not** themselves establish the required product bound on per-route capacity events and inherited history, on all supported word sizes, or reserve the needed one-event counter headroom before a survivor allocation. No source-wide amortized event theorem connecting those guards to G/J was found or derived. A finite number of routes is not the desired numeric inequality.

## Exact obstruction and economy audit

Two different attempts—induction over forward checked events, and a bound from actual route/row identity dimensions—leave the same construction premise unestablished:

> For every admitted constructor history, before a nested reserve that may increase capacity, the ledger owner establishes the branch-specific growth/rebuild headroom required by rollback: `G+max(T,K)` and `J+max(T,K)` for nonincoming recovery, and both the survivor prefixes `G+K`/`J+K` and recorded-event totals `G+E`/`J+E` for incoming recovery. E includes a failed post-reserve event even when its newly changed row will be dropped.

Its exact numerical consumers are the inequalities above. Owners are `record_incoming_bound_capacity_growth`, the extrusion/ordinary-bound reserve callers, and `rollback_route_transaction`'s history reconciliation. The missing evidence is a construction-level headroom/event-budget invariant covering both prior incoming histories and the closed nonincoming retained owner; a successful earlier preflight and GraphState census equality are insufficient.

Under `compiler-engineering.md`, this is A correctness when W requires normal rollback return. It is not retired, weakened or reclassified. The compiler already knows the relevant counts and allocation event at the reserve owner, so another equivalent post hoc MAX-state probe or larger census reconstruction would leave that owner premise untouched. No third equivalent proof attempt was made. Any proposed repair or policy change remains with the primary and its independent design/review path.

The ledger theorem remains **OPEN on this precise premise**. This packet supplies neither a constructor-qualified counterexample nor proof that cumulative counts actually exhaust on a supported source. The original W/A3 remains OPEN independently for its semantic inverse, all-source scheduler, incidence and lifecycle obligations.

## Independent review and repair

A fresh compiler-referee found no blocking or major issue in the derivation.
The reviewer confirmed the `K≤T+1` source argument, the conditional byte
census reasoning, the branch-specific rollback inequalities, and that the
headroom premise remains genuinely open. One minor wording issue was accepted
and repaired above: the newly changed surviving-lane case belongs to the
nonincoming branch, while incoming rollback also needs event headroom for a
failed growth on a dropped row. This repair sharpens the same conditional result
and does not promote its theorem status. The reviewer did not assess semantic
inverse totality, allocator applicability, all-source scheduling, lifecycle
publication or the original W/A3 theorem.

## Frozen inputs, checks, runtime and handoff

The skill, `.codex/agents/prover.toml`, registration/config and required orchestration, research, design-authority, compiler-engineering and Git-concurrency rules were read by this continuing leaf; unchanged routing/policy reads are carried forward. Requested routing: ordinary prover, `gpt-6.1-sol`/high. Observed effective model/effort metadata: **unknown**. No Astra, override, reload, nested process or child launch.

| Exact input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `7ace990203b77f1b8aad185e8cdbb2cdac90b967e38479774b7081e45c9429ee` |
| `candidate_extrusion.rs` | `a76979f01feaf76ffa351625b0443802fca3e6e2b0288b55e274d7538ae22ead` |
| `candidate_scheme.rs` | `b15d72a5be0f82b2dba37b12fdc3e11a555253ff92ae7aa615b05aaa00380768` |
| Frozen W/A3 falsifier | `093f2d3ef7ea4d3b206939c5dc8475cfbe793e25f3c01682c5b06d4f2afa59ad` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Original composition at current baseline | `4344694f4b8a8c4a225aae83d3c39fcf242f92c2ff32f0ae059d84ad85ff9222` |
| Handoff derivation | `052ac8e6499b116f4ec7adc8e9c935ee04f02c8a27419428a4659514a7c12357` |
| Reviewed rollback lemma | `2d526b7df88acedd18c306e6ae5bad15314eed6451d4dd87eddc53c74711cdf7` |

Checks: exact SHA-256 input comparison; plain-file HEAD/ref read; bounded `rg` counter-owner inventory and `sed` reserve/journal/preflight/rollback/constructor/test-body reads; static arithmetic derivation; final dependency and leased-note checks. No tests, builds, executable probes, formatter, Git mutations, compiler/test/shared-record edits or delegation. Test expectations are read as encoded caller behavior only. One leaf, short read/hash processes, zero sustained compute or performance samples; CPU/RSS unmeasured. This resumed packet started at 01:14 UTC and stopped within its 20-minute ceiling.

Excluded/unverified: allocator/stdlib applicability, unconditional history headroom, whole-session sampled census publication, preceding semantic inverse totality, all-source admission/recomputation, §4 incidence, authentic §7 lifecycle/publication, complete Call meaning, hygiene, soundness, required principality and production cutover. The earlier sampled-session-census investigation is outside this new lease/claim and is not claimed completed here.

One next action: primary assigns the actual reserve/accounting owner the construction-level headroom invariant or adjudicates a minimally scoped implementation repair, while preserving the original theorem and obtaining fresh independent review of this reduced premise.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-retained-wa3-ledger-headroom-proof.md`.
- Baseline SHA: `d99d90ba32471d58cb4c8b9d77ab8266804736fd`.
- Changed dependency hashes: none authored or observed in this packet; frozen hashes above.
- Claim/review status: producer derivation independently reviewed; one minor wording repair accepted. Conditional derivation and exact source-construction obstruction only; no theorem promotion; ledger premise and original W/A3 OPEN.
- Checks already run: source/ref/hash reads, counter-owner and constructor/consumer inspection, static derivation, note scope/whitespace checks. No executable verification.
- Proposed checkpoint message: `research: localize retained rollback ledger headroom premise`.
- Shared-record deltas left to primary/curator: record the source-derived K≤T+1 gap and exact branch inequalities; preserve historical-event versus live-capacity distinction; keep source headroom and W/A3 OPEN with the reserve/accounting owner. No shared records edited.

Artifact frozen after final checks; no further writes planned.
