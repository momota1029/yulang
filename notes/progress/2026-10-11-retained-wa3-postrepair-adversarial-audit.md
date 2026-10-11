# Retained W/A3: post-repair adversarial source audit

Date: 2026-10-11
Status: independently reviewed bounded source characterization; no constructor-qualified counterexample found in the inspected inventory. Original W/A3 remains OPEN.
Producer: leaf `/root/wa3_postrepair_adversarial`; no delegation or compiler authority.
Baseline: `d7e87c63723213550ac28ddab45e2ef47ce17f6e`, branch `research/simple-sub-intrusion`.
Exclusive lease: this note only. Budget: one static pass, at most 20 minutes wall time, one lightweight process at a time; no executable experiment, test, build or Cargo.

## Objective and governing statement

Try to bypass the new pre-reserve history guard through an actual bound constructor, or find an earlier semantic inverse escape in Q/D, retained F, replay receipt or parent cursor. Method: enumerate bound allocation/accounting producers, check guard-to-reserve ordering, then inspect the named ownership seams and their reverse order. The earlier broad absence search is not repeated.

Authority is user-approved [private candidate suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md) §6; §3 fixes completion/innermost ownership and §4 fixes the saved-count/live-canonical restoration order. Accepted approval is “承認して実装を進めて”. The exact parent is [nonterminal composition](2026-10-11-nonterminal-drain-owner-composition-proof.md), “Frozen objects, statement and exclusions” and H1/W, with [handoff](2026-10-11-retained-parent-handoff-proof.md) A3/A4. The [earlier falsifier](2026-10-11-retained-parent-wa3-rollback-falsifier.md) and [headroom derivation](2026-10-11-retained-wa3-ledger-headroom-proof.md) supply prior results and exclusions, not assumed closure.

Keep L/G/U, B/emission/raw endpoints/m/n, R/ordered finite H/q/c, a=(R,i), F/j, arbitrary finite ordered Q/A with `0≤d≤p≤|A|`, atomic diagnostic checkpoint projection D, both processing scopes P and C. Source scopes, binders, occurrence/cause, context, fiber, attachment, provider, witness and residual lineage stay distinct. Constructor-valid histories may begin at committed Running or Ready; neither a successful rollback premise nor a unique-operation-ID restriction is added. D includes the ordered diagnostic delta and its mathematical index, covered memos/errors; it does not mean identical HashMap bucket layout or retained contents of temporary diagnostic-completion scratch.

## Reserve-to-reconciliation coverage

All locators below are at the baseline in `crates/yu-solver/src/`.

| Actual producer / lanes | Admission before allocation | Post-reserve and rollback consumer | Finding |
| --- | --- | --- | --- |
| `candidate_extrusion.rs:411–429`, macro expanded at `465–568`: four Value and four Effect lanes | Old-row journal admission precedes the macro; `preflight_bound_capacity_growth` immediately precedes `reserve_f5b(...,1,...)` | Actual old/current capacities pass to `record_incoming_bound_capacity_growth`; push and flags follow success. Outer rollback truncates old rows and removes new rows. | All eight macro arms share the guard. No branch-specific bypass found. |
| `lib.rs:11694–11733`: ordinary Effect direct lower/upper pair | Both rows journaled; guard runs separately before each reserve | First capacity recording completes before second guard. Both logical pushes follow both recordings. | A first reserve cannot spend the second reserve's checked headroom unnoticed. |
| `lib.rs:11771–11789,11829–11847`: ordinary Effect exact lower/upper | Guard on the selected lane before its reserve | Same capacity recorder, then insertion/flags | Both atom branches covered. |
| `lib.rs:13751–13791`: ordinary Value direct lower/upper pair | Both rows journaled; guard runs separately before each reserve | Same sequential recording and delayed pushes | Same second-reserve discrimination as Effect. |
| `lib.rs:13839–13858,13917–13936`: ordinary Value exact lower/upper | Guard before reserve | Same recorder, then insertion/flags | Both atom branches covered. |
| `lib.rs:14114–14147`: guard owner | If `len==capacity`, checks current G/J +1, attempt E +1, retained T +1 for old rows; incoming also checks checkpoint G/J +(E+1) | No allocation or counter mutation in this function | Failure leaves the lane unallocated. `len<capacity` is a legitimate no-growth case for reserve(1), conditional on ordinary Vec behavior. |
| `lib.rs:14205–14385`: recording owner | E increments on physical capacity change before byte preflight; guard already checked it | Payload/G/J/T publish only after checked arithmetic; resource sampling or post-reserve error can still fail the route | Byte failure remains possible as an operational failure; it no longer implies missing one-event history headroom. |
| `lib.rs:9530–9641`: rollback consumer | Old-row snapshots supply entry capacities; route-created rows already removed | K survivor-lane increments followed by incoming checkpoint+E or nonincoming additional `T.saturating_sub(K)` | Earlier missing numerical branch is addressed at the actual reserve owners; byte representability remains separate. |

The source-wide symbol inventory found no other non-test call of the capacity recorder beyond these forward sites and rollback. Direct literal nested pushes found in `shadow_apply.rs` are test fixture construction (the inspected block constructs an `InferenceSession::new` in a test); they are not admitted retained-route constructor transitions. Macro-generated pushes are covered by the explicit macro read. Ordinary effect pushes through a selected vector were inspected in their owning match rather than inferred from literal-push search alone.

This is bounded source coverage, not a theorem of all possible future compiler mutations. The relevant forward counter assignments found outside tests are the recorder; rollback assigns its restored totals. Snapshot observation assignments do not reset the live ledger between a guard and reserve.

The discrimination is the *location* of the check. For a route with f successfully recorded growths and one final physically changed lane rejected by byte accounting, the new guard checks current `G+1`/`J+1` **before that last allocation**. Under the forward-ledger invariant current G/J equal checkpoint G/J +f, and `T≤f`, `K≤T+1`, so the nonincoming `max(T,K)≤f+1` increment fits. Incoming's checkpoint+(E+1) guard covers a final event even on a new row later dropped; K≤E makes survivor prefixes fit. If there is no final unrecorded physical event, K≤T≤f. This conditional local argument explains why the old failed-preflight trace no longer attacks the history premise. It is not the primary prover's theorem or an independent review of that theorem.

## Semantic inverse coverage matrix

| Named state / forward seam | Actual reversal | Evidence and residual boundary |
| --- | --- | --- |
| Old row lengths/flags/metadata/levels/marks; `journal_value_row`/`journal_effect_row`, `lib.rs:9241–9336` | `lib.rs:9423–9480`: restore saved fields before new-row truncation | Once-per-row entry snapshot covers inspected bound writes. Exact addressable-capacity byte census is a different premise. |
| Q admission/pop/growth; `lib.rs:12670–12840` | `rollback_workspace`, `12770–12805` | Undo reserved before queue mutation; reverse chronological pushes/pops and old allocations restore order. Reverse pushes rely on restored lengths fitting owned old capacities. |
| D delta/index admission/growth/wholesale clear; `12710–12759,13490–13516` | Same inverse loop; rebuild mathematical index from restored ordered delta | Partial clear failure after DeltaClear but before IndexClear has an already-owned inverse. Completion scratch is temporary and cleared only after this named D reversal. Valid collection operations/no hidden individual frontier deletion are shared assumptions. |
| F current/stage/pending/A/d/p/destination, Running stages; `prepare_nonterminal_drain`, `12163–12195`, `step_typed_drain`, `12198–12305` | Context frame undo, `candidate_context.rs:1588–1598` | `prepare_typed_drain_update`, `1748–1766`, retains original F/ack allocation before replacing it. Newly created F is removed by frontier truncation. No missed snapshot found in the exposed stage seam; atomic helper mutation coverage is not exhausted here. |
| Acknowledgements, ReturnReady removal and Running→Ready; `lib.rs:12522–12615` | Old F restored before new-F truncation; replay undo follows at `candidate_context.rs:1604–1610` | Terminal frame and exact replay-return undo precede receipt publication/pop. Removal does not discard original F held by undo. Committed Running and Ready are both included. |
| Ready delivery, `candidate_context.rs:3044–3056`; replay q/c/wait/retired | Replay snapshot, `1839–1849`; reversal at `1604–1610` before operation-frontier removal | Delivery validates exact a/j/q/c, prepares wait undo before clearing Ready. Receipt is a stored completion, not reconstructed from transition count. No escape found in that seam. |
| B replay pointer/n/retired; `candidate_extrusion.rs:697–765` | Restoration undo at `candidate_context.rs:1599–1603`, then replay undo/new-operation removal | Update prepared before retirement, child step or parent advance. Exact replay/restoration link checked before child execution. Incidence stability for canonical owner at saved n remains the separate §4 gate. |
| L cursor and immutable G/U; `candidate_scheme.rs:1466–1500` | `lib.rs:9375–9389` restores cursor/source before row/workspace reversal | Actual closed helper keeps L in its vector through fallible child/receipt calls. Existing Local-presence/GraphState-refresh lemma is prior evidence; that attack is not restarted. |
| Covered memo/completion/diagnostic edges; `candidate_intrusion.rs::journal_candidate_memo` and typed admission | `candidate_intrusion.rs:103–134` restores old memos before outer new-key removal at `lib.rs:9490` onward | New-pair versus old-memo ownership supplies the inspected order. Full atomic dispatch/memo replacement coverage is still an inverse-law premise. |
| Context/effect creation logs, bound evidence, origins, processing P | Context rollback `1581–1680`; effect rollback `181–210`; intrusion rollback `103` | Frame/restoration/replay undo precedes destruction of new operations. Both processing scopes restore from owned checkpoints. Exact map/log membership and reverse assertion validity for every atomic producer are not proved by reading these reverse methods. |
| Store facts/receipts/provenance/terms | `lib.rs:3316–3351`, before graph rollback | New fact keys removed, new receipt interval removed, frontiers/counters reset, term owner reversed. This pass reads outer reversal; it does not exhaust all term constructors. |

`rollback_route_transaction` still takes its journal before store/context reversal and has earlier fallible Local/GraphState refresh sites. Their admitted closed-owner success is supplied by the existing reviewed rollback lemma, not by the new headroom guard. Bound reconciliation errors accumulate; `lib.rs:9666–9700` reverses retained Q/D and installs the spare before returning `accounting_error`. Counter repair alone therefore cannot establish normal semantic inverse return or byte reconciliation.

## Exact residual owner and stopping point

No minimized constructor-qualified countertrace was found in this one inventory-and-seam pass. Arbitrary MAX counter/byte assignments in fixtures are not reachability witnesses; no new such state was proposed. The already identified missing headroom premise is materially changed by this repair, so another equivalent MAX probe would not discriminate it.

The residual W/A3 inverse premise is at the **atomic forward owners**, particularly `candidate_context_execute` / `candidate_context_execute_relation` (`candidate_context.rs:2733` onward), `settle_candidate_intrusion` (`candidate_intrusion.rs:358` onward), effect origin/capture mutation owners consumed by `candidate_effect.rs:181–210`, and store term construction consumed by `lib.rs:3351`. For each constructor-valid retained invocation, these owners must establish complete matching undo, validity of reverse map/log assertions, and allocation-safe restoration. The listed snapshots and reverse methods do not establish that universal producer/consumer correspondence. This pass did not exhaust those bodies, and finding no exposed Q/F/receipt seam does not discharge their premise.

The other residual is the **byte owner**: exact entry nested allocation census and representability of the surviving deltas consumed at `lib.rs:9530–9603`. The repaired guard checks history counts, not byte charge. Valid uniquely owned addressable collection allocations may support the independent byte argument, but allocator/stdlib applicability and induction through prior failed histories were not established here. Prior GraphState census equality cannot replace this nested bound ledger.

Recommended next action: apply the independent headroom proof to its exact guarded producer inventory, then assign a constructor-directed inverse induction to the above atomic mutation owners, rather than repeat this bounded absence search. Preserve the original parent quantifiers and keep byte, semantic inverse, §4 incidence and §7 lifecycle gates distinct.

## Independence, commands, resources and frozen dependencies

Source supplies real operational ordering. There is no independent executable oracle, finite transition model, randomized search, mutation run or enumeration. Existing test bodies encode implementation bookkeeping and manually modified ledger operands; they are static corroboration only. Shared assumptions are valid Rust collection semantics, valid owned IDs/frontiers, nonconcurrent mutation of this session, and the separate already-reviewed Local/GraphState premise. Omitted: complete atomic-method coverage, all admitted scheduler states, stdlib/allocator verification, panics/corruption, full source/SCC driver, lifecycle withdrawal/recomputation/publication, production certificates, Call meaning, hygiene, soundness, principality and cutover.

Commands run: bounded `rg -n` producer/counter/nested-write inventories; `sed -n` targeted forward/inverse owners and prior proof sections; `cat` the three required rules and skill; read-only `git rev-parse`, scoped `git diff d7e87c637 -- <dependencies>`, and `sha256sum`. Dependency diff was empty. A broad initial task/index capture truncated; relevant governing statement and source seams were reread narrowly. No test/build/Cargo/formatter/scratch execution/Git mutation. One leaf; serial short read/hash processes; zero sustained compute and zero performance samples. CPU/RSS and exact process-total count unmeasured. Work completed within the 20-minute ceiling. Runtime model/effort not independently observable; no override or launch.

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `31c66d1bc9cc101c6174424f5f11b7cbeb6eb497448e0a4b09b683adbacb9dd9` |
| `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |
| `candidate_scheme.rs` | `b15d72a5be0f82b2dba37b12fdc3e11a555253ff92ae7aa615b05aaa00380768` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Original composition | `4344694f4b8a8c4a225aae83d3c39fcf242f92c2ff32f0ae059d84ad85ff9222` |
| Earlier falsifier | `093f2d3ef7ea4d3b206939c5dc8475cfbe793e25f3c01682c5b06d4f2afa59ad` |
| Headroom proof | `28f595f0bf3b787d6c173dce7ee2a567e6790322626b28a44b4cc1a03741c51e` |

## Independent review

A fresh compiler-referee reviewed the frozen artifact at SHA-256
`a4613487067cb350fd9387bca51160edd2ac574bee510bef881aa52bd86f7420` and found
no blocking, major or minor findings. The reviewer confirmed the inspected
reserve coverage and inverse-seam map, while explicitly leaving atomic
constructor induction, allocator applicability, scheduler states, §4
incidence, lifecycle/source/SCC paths and theorem certification unreviewed.
This closes review of the bounded characterization only; the original W/A3
inverse and byte premises remain OPEN.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-retained-wa3-postrepair-adversarial-audit.md`.
- Baseline SHA: `d7e87c63723213550ac28ddab45e2ef47ce17f6e`.
- Changed dependency hashes: none authored or observed relative to the pinned baseline; hashes above are the post-repair inputs, not the earlier pre-repair compiler hashes.
- Claim/review status: independently reviewed bounded source characterization and conditional local arithmetic explanation; no constructor-qualified refutation, theorem closure or production promotion.
- Checks already run: exact branch/HEAD, scoped dependency diff/hash reads, guarded-producer inventory, named semantic inverse seams and note whitespace/scope check. No executable verification; primary owns verification/review.
- Proposed checkpoint message: `research: audit retained rollback owners after headroom repair`.
- Shared-record deltas intentionally left to primary/curator: associate guarded producer coverage with the repaired history premise; retain atomic producer/inverse correspondence and nested-byte census as explicit separate residual owners; retain original W/A3 OPEN. No shared files edited.

Artifact frozen after final dependency and lease checks; no further writes planned.
