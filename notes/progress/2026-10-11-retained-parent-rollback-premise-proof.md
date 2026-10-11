# Retained Local rollback: outer reconciliation premise

Date: 2026-10-11
Status: independently reviewed bounded constructive source derivation; no findings in the stated early-exit scope. The original parent theorem remains OPEN; no certification or semantic authority is claimed.
Producer: leaf `/root/retained_rollback_premise_proof`; no delegation.
Exclusive output lease: this note only.
Packet baseline: `eb502ad3db5e3df7691dba1349f67bfd607612fc`. Observed branch ref at entry: `research/simple-sub-intrusion`, `146025ddcafeeae412d9a8b8da5dda536d30f250` (the primary identifies its advance as policy-only). Actual compiler inputs are the frozen worktree hashes below.

## Objective and frozen statement

Address the two possible early exits in outer rollback identified by [the retained-parent source bridge](2026-10-11-retained-parent-handoff-source-bridge.md), “Rollback-success qualification”: absence of the retained Local at `last_mut`, or checked `GraphState::refresh_bytes` failure before ordered workspace reversal. The method is direct ownership and allocation-census induction over actual construction, mutation and inverse order. This does not repeat the acknowledgement-prefix proof or assume that rollback succeeded in order to prove these exits impossible.

Authority is the approved [private suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md) §§3/4/6 and its recorded user approval, “承認して実装を進めて”. The [original composition](2026-10-11-nonterminal-drain-owner-composition-proof.md), “Frozen objects, statement and exclusions” and H1–H5, fixes the parent obligation. The [completion-barrier derivation](2026-10-11-retained-parent-handoff-proof.md), A1–A5, preserves the primary's accepted correction: terminal acknowledgements consume before ReturnReady; Ready delivery releases a post-consumption barrier and never acknowledges twice.

Keep all original binders: retained Local L, graph G and fresh remaps U; accepted restoration B/emission e, raw endpoints, original opposite count m and n; active replay R and ordered finite H; child occurrence a=(R,i), F/j, finite ordered A with 0<=d<=p<=|A|; finite ordered Q, atomic diagnostic projection D, both processing scopes P, and exact route checkpoint C. Original source scopes, contexts, fibers, attachment/provider/witness/residual identities remain distinct. Neither repeated relations nor shared operation IDs identify acknowledgement positions.

For **every constructor-valid invocation of the actual closed retained Local driver**, and every finite Q/A/H and stage it accepts or rejects within that invocation, failure after route entry cannot take either early exit above. If the existing semantic inverse primitives return normally and satisfy their exact inverse laws, outer rollback reaches ordered workspace reversal and restores the named C projection, including original ordered Q/D, F/destination, replay slot/receipt, B/L cursors and P. This result does not require the later accounting reconciliation to return Ok. To obtain the stronger A3 wording that rollback itself returns Ok and the original route error is preserved, the remaining reconciliation arithmetic premise below is still required.

This is a bounded source lemma applicable to W/A3, not a replacement statement for the original theorem. Its source domain is exactly the bridge's existing `candidate_test_retained_local_step` owner, plus the fixed synchronous Local continuation steps used by its constructor. It does not assert a general retained source/SCC scheduler exists. The driver really is test-only and requires one existing unfinished Local; that fact is a correspondence boundary already present in source, not a restriction added to Q/A/H or to ordinary source inference. Starting in Running or Ready is permitted. No restriction to routes whose rollback is already known successful is used.

Excluded: arbitrary mutation callbacks supplied to the generic test-only `resume_typed_drain_route`; semantic correctness or arbitrary internal interruption of Transport/Context/Dispatch/extrusion/Diagnostics; incidence deferral under external suspended mutations; lifecycle withdrawal/recomputation, publication and authentic §7 coverage; full source reachability, termination, Call, hygiene, soundness, principality, production certificates and F5 cutover. No allocator-address equality, universal capacity equality or historical-peak equality is asserted.

## Constructor-owned accounting invariant

Let T be the nonnegative integer expression **actually evaluated** by `GraphState::refresh_bytes` (`candidate_scheme.rs:238–260`): the five top-level vector capacity terms, every occupied immutable graph's `Graph::bytes`, each stored fresh route's graph and row-vector terms, each Local route's graph and rows, and each retained Local's graph and `FreshUse::bytes`. This is a mathematical reading of the existing accounting function, not a proposed reconstruction relation or runtime field. Let M=usize::MAX.

At an admitted, successfully constructed Local continuation entry, T is representable. Its constructional witnesses are:

- `start_candidate_graph` (`674–690`) calls checked `refresh_bytes` before installing the state; this establishes the base census.
- SCC graph publication (`899–912`) checks every new graph byte sum and its addition to retained bytes before installing graphs. Replacing an occupied graph could only make the actual census smaller than this nonnegative charged upper bound; it cannot invalidate representability.
- Incoming fresh-route construction (`1285–1312`) checks the top-vector capacity growth, graph and row bytes and their combined charge before publication. A successful publication uses exactly those owned allocations.
- Local construction (`1362–1382`) reserves the Local vector, charges its actual capacity delta, constructs G/U atomically, checks `retained_bytes + G.bytes + U.bytes`, and only then pushes L. Successful pause preserves this existing L and its immutable allocations. The proof uses these checked construction steps, not the test script's later assertion of accounting equality.
- Final Local publication (`1518–1537`, then `commit_local_use` at `228–236`) preflights replacement capacity and its charge. Commit moves G and the already allocated fresh row vector into the Local route and releases only the remaining construction maps. Thus the census changes by the same nonnegative released amount; it remains representable.

These steps establish T<=the representable construction charge for successfully emitted continuation entries. An arbitrary manually assembled GraphState with a stale byte count is not constructor evidence. A failed initial Fresh-route construction has its own wider rollback obligations; this lemma does not treat its absence of L as an already constructed retained route. The original parent fixes an **existing** L/G/U. No live-memory/address-space bound, allocator success assumption about a future restoration, or universal session-capacity restoration is needed for the census lemma.

Successful retained steps below preserve the census, except the preflighted final publication change. Failed retained steps restore its exact entry inputs before refresh. Induction therefore supplies the same representability witness at each later retained invocation, including after an earlier failed invocation once the imported semantic inverses return. The induction imports their normal return, not the outer `last_mut` or refresh outcome being proved.

## Forward ownership and exact inverse order

### 1. Local cannot disappear at the error boundary

`candidate_test_retained_local_step` (`candidate_scheme.rs:1466–1499`) rejects an active journal and validates one unfinished L before `begin_route_transaction_for(RetainedResume)`. Route entry snapshots L's cursor (`lib.rs:9136`).

In its restoration branch, L stays at vector index zero throughout restoration stepping, drain work, terminal acknowledgement, ReturnReady, receipt delivery and all fallible returns. Only L's cursor is updated. In its no-restoration branch, the queue/drain checks return errors before a pop; otherwise the driver pops L, calls the atomic Local step, then pushes the **same frame** before `result?` (`1491–1494`). Pop does not shrink vector capacity, and the original length fits that capacity. Push needs no reserve and invokes no fallible user operation. The synchronous Local constructor/continuation has the same pop/call/push-before-`?` order (`1390–1401`).

The only successful-removal owner is `commit_local_use`. It is called by `finish_route_transaction` only in its Ok arm (`lib.rs:9219–9222`), after the operation returned successfully. The Err arm instead invokes rollback (`9235–9237`). Thus even a frame whose `complete` flag was just set is still present on failure. No early publication commit occurs in the operation closure.

The complete field-write inventory in production candidate modules finds no Local removal in the child call cone. The broader generic test resume callback can deliberately clear L, so this argument is for the actual closed owner, not every closure accepted by that generic helper. That distinction prevents a callback assumption from being mistaken for a constructor theorem.

Consequently outer rollback's `last_mut` at `lib.rs:9377` succeeds and reinstates the checkpoint cursor. This conclusion is independent of lawful acknowledgement order, child relation equality, the number of queued tasks, and whether a child operation returned a validation/allocation/accounting error.

### 2. Child work cannot change the immutable census

The actual driver calls either `candidate_step_bound_restoration_child(..., true)` or `step_candidate_local_use`. Restoration and typed work mutate the intrusion/effect/context owners, queue, diagnostics, ordinary bounds, semantic memos and retained stages. None is included in GraphState's graph/route/Local immutable census. `FreshUse` is passed immutably into `begin_candidate_fresh_bound` (`candidate_scheme.rs:1221–1270`); G/U are retained, never reconstructed. The typed stage entry and dispatch (`lib.rs:12142–12287,12290` onward) do not schedule source actions or publish SCC graphs.

Searches for all `.graphs`, `.routes`, `.locals`, `.local_routes`, `.local_use` references in production candidate modules and `lib.rs` locate the graph/source publication owners separately. The closed retained driver reaches none of SCC publication, incoming-use route publication or Local installation. Its census-changing possibility is only the final Local-route vector growth below. Intrusion rollback changes `state.intrusion`, not these immutable allocations (`candidate_intrusion.rs:106–133`). Effect/context rollback similarly changes its own objects (`candidate_effect.rs:182–210`, `candidate_context.rs:1585–1675`). No inference from a successful semantic query is used to establish this separation.

### 3. Final publication growth restores the original allocation without reserve

Let N be the entry `local_routes.len` and K its capacity, N<=K. A Local step reaching final publication can grow only if N=K (`candidate_scheme.rs:1520–1521`). It:

1. computes/reserves the replacement capacity fallibly;
2. checks its actual byte delta and next retained charge;
3. validates active journal and empty allocation-undo slot;
4. moves the existing N entries into the replacement;
5. stores the now-empty original allocation in `candidate_local_routes_allocation`;
6. samples resources, then marks L complete.

Errors before step 4 have not installed a new allocation. Errors after step 5 leave the original allocation owned by the journal. Moving N entries cannot grow a replacement already reserved for at least N; no fallible call separates moves and ownership registration. There is no new Local route pushed until the outer Ok commit.

Rollback first truncates the replacement to the entry N, then appends those N entries to the retained original allocation and swaps it back (`lib.rs:9383–9386`). The original allocation is empty with capacity K>=N; append therefore needs no allocation. Entry order is unchanged by both moves. Each graph and row vector moves as an owned object, preserving its capacity. The discarded replacement is dropped only after old ownership has been recovered. If the capacity preflight or resource sample failed, this same case split applies.

Rollback truncates ordinary `routes` to its entry length (`9388`); within this driver that vector and all graph/Local slots were unchanged. The retained Local vector has its original length/capacity, G/U capacities and content. Its cursor was already restored. Thus **every operand and every enumeration position of refresh_bytes now equals its entry operand**, even when the route failed after setting Local complete or after Ready delivery. This limited census equality does not imply equality of semantic-map, typed-stack, undo-vector or other session allocations.

### 4. Checked refresh cannot newly fail

After the preceding inverses, refresh evaluates the same five capacity multiplications and same nested graph/fresh byte expressions, in the same order, as the representable entry census. All terms are nonnegative and the entry total T<=M. Every partial sum and constituent product is consequently <=M. Re-evaluating them cannot overflow. It sets `state.retained_bytes=T` and returns Ok at `lib.rs:9389`.

This derives arithmetic success from unchanged constructor-owned inputs. It does not assume that a resource sample succeeded during the failed operation; samples may fail because they additionally count new semantic/undo/workspace storage. That additional storage is not enumerated by this refresh function. Nor does it infer that every allocation in the entire route shrank back to its original capacity.

The earliest-return threat identified in the source bridge is therefore removed for every failed invocation of this closed retained owner, subject to normal return of the earlier imported inverse primitives. No admitted-envelope Local-loss or refresh-overflow counterexample was found by this source derivation. Manually clearing L or inventing overflowing capacities would leave the constructor/control envelope rather than refute it.

## Workspace reversal and exact named equality

The real order is material. `rollback_route_transaction` first takes the journal and rolls back store; next intrusion/effect/context reversal restores F (including original acknowledgement allocation/destination), B, replay slot/receipt/q/c/retirement, creation frontiers and P; then Local/source/routes/census are restored. Ordinary bound/memo/error inverses follow. Only later does `rollback_workspace` reverse Q/D (`lib.rs:9666–9671`). Q is not yet restored at the time of refresh, but refresh neither reads nor accounts Q.

Context reversal applies old frame snapshots in reverse order before truncating new frames, then B snapshots, then replay snapshots before removing newly created operations (`candidate_context.rs:1585–1614`). This is the slot/F/receipt inverse owner supplied by the prior bridge. It restores a checkpoint committed after acknowledgement to that already-consumed Running state; it does not arbitrarily rewind consumption to selection. Context/effect processing checkpoints restore both P lanes.

Workspace push/pop/admission/growth/clear events are reserved and recorded before mutation (`lib.rs:12650–12748`, `enqueue_item`, `clear_diagnostic_scratch` at `13470` onward). The inverse loop (`rollback_workspace`, `12750`) uses reverse chronological events: undo enqueues remove the corresponding end, undo dequeues restores the exact item at the front, and undo growth returns contents to the retained old allocation after later operations have been reversed. A restored pre-growth length fits the original capacity, so reverse push/append/extend needs no growth. Clear inverses restore the original ordered delta/index objects. Final index rebuilding at the end of that function clears tombstones and inserts exactly the ordered delta's keys into its retained allocation; it restores the mathematical index rather than claiming identical HashMap bucket arrangement.

Therefore, importing the existing journal coverage/inverse laws, the named projection is exactly C: ordered Q and diagnostic delta, its mathematical index, covered memo/errors, F's current/stage/A/d/p/destination, replay slot and exact receipt, B/L cursors and handles, and P. This is stronger than equal lengths or unordered work sets. The proof does not require H3 for rollback of a failed exact-index check: a malformed next acknowledgement can fail and still reverse its preparation/earlier effects. H3 is needed separately for successful completion and parent advancement.

## Remaining rollback and original-parent premises

The result eliminates the **outer Local validation and refresh arithmetic** qualification for the actual retained owner. It does not erase all of W/A3. The remaining exact premises are:

| Premise | Actual owner and precise remaining evidence |
| --- | --- |
| Semantic inverse correctness and normal return | Store rollback; intrusion/effect/context undo; ordinary bound rows, pair/error keys and replay/diagnostic mutations in `lib.rs:9368–9525`. Stored checkpoints alone do not prove every atomic forward primitive journals every semantic mutation or that its reverse `expect/assert/insert` is valid and allocation-safe on all relevant paths. The frame/B/replay inverse order above is source evidence, not that global proof. |
| Workspace event coverage and reverse capacity | Existing Q/D owner and `rollback_workspace` at `12750`, with clear owner at `13470` onward. The reverse-capacity argument covers the shown events; it relies on the fixed driver using these entrypoints for every covered mutation and on the ordinary collection operations completing normally. Arbitrary direct test closure writes are outside this bridge. |
| Late accounting **return** success | `lib.rs:9530–9640` reconciles surviving ordinary bound capacities and growth/rebuild histories. `record_bound_capacity_growth` at `14073` checks byte/counter increments. Errors are accumulated in `accounting_error`, **not propagated with `?` before workspace reversal**. `9700` returns this error only after workspace reversal, scratch cleanup and journal-spare installation. To claim outer rollback returns Ok, establish these checks are representable from their own bound-capacity/history owners. GraphState census equality does not establish this different ledger. No allocation/address-space argument or counter limit is assumed here. |
| Lawful completion H3/A1 | The F acknowledgement projection onto each replay must yield successive exact indices beginning at its current consumed cursor; descendants must complete before those events; no outside owner consumes them; replay/restoration operations remain live through their final owner/undo. Preparation merely checks consumed<=index<queued. The additional Running/Ready checks and exact `consumed==index` validation reject bad orders; they do not prove constructors always generate the lawful full sequence. |
| Atomic semantic-stage H4/A2 | Exact source semantics and undo of Transport/Context/Dispatch/extrusion/Diagnostics at the admitted whole-call boundary. No internal continuation was invented by this note. |
| Incidence and scheduler bridge | Contract §4's saved count/live canonical lookup under allowed suspended mutations; actual all-source retained scheduler and lifecycle/§7 owners. These remain unchanged by rollback census reasoning. |

In particular, a late reconciliation error is **not** the feared partially unreversed Q/receipt state: by then context and workspace reversal have executed. It can override the original operation error because `finish_route_transaction` uses `rollback_route_transaction()?`; that is a remaining operational/accounting question, not proof that C failed to restore. Accounting fields that intentionally retain capacity growth or peaks are outside the exact pre-route equality claimed in the source bridge. This note does not declare the stronger contract's entire accounting obligation proved.

The precise result to apply is: replace the two early-success assumptions by the constructor-owned Local/census lemmas; retain semantic inverse and late reconciliation success where the parent needs them. The full original theorem still requires H2/H3/H4, current-representative incidence and independent review. Do not promote it merely because these two rollback exits have been ruled out.

This is one different constructional attempt at the localized premise. The earlier conditional compositions left rollback imported. Under `compiler-engineering.md`'s proof-obligation-economy audit, exact route recovery is A correctness, while a new proof-only reconstruction of G/U or a universal allocation-capacity equality theorem would add unnecessary D/C work. The owning phase already retains immutable allocations and original publication allocation; using that evidence preserves ordinary inference. A further equivalent census proof will not close late bound-ledger history or atomic semantic-journal coverage; send those exact premises to their owners.

## Independent review

Fresh compiler-referee `/root/retained_rollback_proof_review` reviewed the frozen note at SHA-256 `e9838c87b55c918bc1ffa369179a56fe68d04c43859a4d5df8499bf248043cf8` against the original quantified composition and current source. It reported no BLOCKING, major or minor findings within the bounded lemma. The reviewer accepts only the two early-exit exclusions for constructor-valid invocations of the closed retained Local driver, conditional on semantic inverses returning normally. It confirms the Local-presence argument and restoration of the exact census before `refresh_bytes`; the disjoint-address-space premise from the complementary falsifier is not needed for this narrow refresh claim.

The review does **not** discharge semantic inverse coverage, later `accounting_error` success, lawful H3 acknowledgement lineage, atomic stages, incidence stability or the broader scheduler/lifecycle bridge. Those remain OPEN under the original parent. This review is not certification of W/A3 or the parent theorem.

## Frozen dependencies, checks and resources

The primary explicitly authorized the two amended current compiler files after the initial hash comparison: completed test-only attribution-reason repair. During this packet the primary additionally authorized an isolated `cfg(test)` incoming-sample trace event around actual workspace-undo vector capacity growth in `reserve_workspace_undo`. The inspected added event is between reservation and the existing capacity observation; it does not change Local/census ownership, workspace mutations or inverse ordering. This amended `lib.rs` hash is recorded below. No failed test supplied by the primary is used as proof or authority. These are the actual inspected hashes; they supersede the older source bridge's production-hash snapshot only for this packet.

| Dependency | SHA-256 |
| --- | --- |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Original composition | `fed59c7525595f3d674aaf7c011362267ae54e0ad5ccae920abaaf60bbcf089a` |
| Conditional handoff proof | `052ac8e6499b116f4ec7adc8e9c935ee04f02c8a27419428a4659514a7c12357` |
| Retained source bridge | `25e114ca4954ec7ac9672df632c0674f36d9589fb0167a7e051b5e9173bd45e3` |
| Earlier workspace bridge | `5831bf8a1cc1363463aae0ac4d78f50737e92f36274cb1261af58def62facdee` |
| Imported prefix proof | `1419b12825c1f555d918829597de6af88ac35f2191d1deb70bc26f7a4c4cc37b` |
| Prefix source audit | `70616b915b5d10532251e3e442e96fc973102755af2937a5bf26ad236b1896cc` |
| `lib.rs` | `effd339a610e9c33185ba16c206bbba094ce372214fe11ceb5baaa0175e77a9b` |
| `candidate_context.rs` | `1b67fa5bab89e4b6d06ca0cd54989ad8f00406962b081e45555b1708ec06932b` |
| `candidate_extrusion.rs` | `a76979f01feaf76ffa351625b0443802fca3e6e2b0288b55e274d7538ae22ead` |
| `candidate_scheme.rs` | `b15d72a5be0f82b2dba37b12fdc3e11a555253ff92ae7aa615b05aaa00380768` |
| `candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |

Checks: read yulang-proofs skill and all requested active rules, actual role/config pins, original theorem/bridge/contract; resolve HEAD using `.git/HEAD` and its named ref as plain files; exact `sha256sum` input comparison; bounded `rg` inventories of Local/census mutations and owning calls; `sed` reads of actual constructors, publication inverse, rollback order, workspace event/inverse, typed stage and restoration owners; final input and note whitespace/lease checks. No Git command or mutation, code/test/shared-record edit, tests, builds, Cargo, executable probe, formatting run, nested CLI or delegation. Broad multi-file capture was truncated initially and the governing rules/notes were subsequently read in bounded separate calls.

One leaf and short read/hash processes; zero sustained compute workloads, compiler processes or performance samples. Work remained within the packet's 40-minute ceiling. CPU/RSS were not measured. Requested routing: normal prover, `gpt-6.1-sol`/high; `.codex/config.toml` registers the role with Sol/high defaults, and the role file omits model/effort pins. Effective runtime metadata is unavailable here: observed model/effort **unknown**. No Astra, hot reload or override-success claim is made. The primary retains verification, review and integration ownership.

Next action: apply this reviewed lemma to the original W/A3 bridge, then assign the exact late bound-ledger arithmetic and semantic inverse-coverage premises to their owning lanes; preserve the parent theorem's OPEN status.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-retained-parent-rollback-premise-proof.md`.
- Packet baseline: `eb502ad3db5e3df7691dba1349f67bfd607612fc`; observed HEAD ref `146025ddcafeeae412d9a8b8da5dda536d30f250`; frozen worktree dependency hashes above.
- Changed dependency hashes: none authored by this leaf. Primary-authorized context amendment `06748bc7...` → `1b67fa5b...`, extrusion amendment `a8316295...` → `a76979f0...`, and isolated lib instrumentation `c0d8a215...` → `effd339a...` are consumed explicitly; no reinterpretation of the earlier bridge's bytes as current-source evidence.
- Claim/review status: independently reviewed bounded constructive early-exit derivation; conditional named rollback composition; original parent OPEN; no self-certification or theorem promotion.
- Checks already run: exact frozen dependency hashes, complete relevant field-write/call-owner inventories, direct forward/inverse/accounting reads, note whitespace/lease inspection; no executable verification.
- Proposed research-checkpoint message: `Derive retained Local outer rollback reconciliation premise`.
- Shared-record deltas left to primary/curator: replace Local absence/refresh overflow qualifications with this bounded constructor argument; retain exact semantic inverse, late bound-ledger return-success, H3, atomic-stage/incidence and authentic scheduler/lifecycle premises; preserve original parent status and capacity scope. No shared task/index/theory/design/rule file changed.

Artifact frozen after final checks. No further writes are planned.
