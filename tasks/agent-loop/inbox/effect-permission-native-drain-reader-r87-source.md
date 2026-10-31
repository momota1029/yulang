# R87 source lane — candidate paired receipt transport

Sprint: `NATIVE-DRAIN-READER-CORRESPONDENCE/20261031-R87`.
Assignment: `/root/r86_source` (reused runtime identity); handoff revision 1.
Outcome class: **candidate owner-local proposal, supported by bounded source equations**.
Worker state on submission: **STOPPED / WRITES STOPPED**. No children, other output paths, source edits or independent-review claim.

## Baseline and authority

Primary-pinned baseline/admission: `9931800b1aed04402049a0e7685630f24b9e5e56`. Corrected admission was committed/pushed by the primary at `d6cbc700c` before resumption; this worker ran no Git command.

Governing contract: `tasks/agent-loop/sprints/native-drain-reader-correspondence-20261031-r87.md`, 6213 bytes, SHA-256 `2ec7f33760b4ef8cdb3ac434dcf415f473a2019f4acf87c25786f77e0fc81261`; specifically “Fixed outcomes and falsifiers”, “Exact lanes and artifact leases”, and “Budget and execution gate”. Corrected manifest: `tasks/agent-loop/sprints/native-drain-reader-correspondence-20261031-r87-inputs-r2.json`, 2756 bytes, SHA-256 `e3d1b0590ea1fb179cc89039665b04d0d4d9bd2ec6a63290df4f90011fe2be96`.

The original dispatch/manifest pinned a stale pre-cleanup contract hash. Initial hash inspection found the mismatch, the worker stopped without writes, and the primary supplied committed Amendment 01. `tasks/agent-loop/history/native-drain-reader-correspondence-20261031-r87-amendment-01.md` records that trailing-whitespace cleanup changed the hash without semantic contract changes. The superseded manifest hash was `c96e2ada0461e0ed5527af4c4d96e697034aa9428420f56c10b6d489825409f4`. No budget reset is assumed.

Only these two Rust files were read in R87:

| Input | Bytes / lines | SHA-256, initial and final |
| --- | --- | --- |
| `crates/yu-solver/src/candidate_context.rs` (C below) | 265778 / 4785 | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_receiver.rs` (R below) | 292001 / 5795 | `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` |

The original A/B quantifiers, accepted source domain, effect hygiene, birth-level qualification, R57/R84 definitions and Root obligation remain unchanged. Root compatibility below uses the contract's declared attached-completed boundary and the prior R86 diagnostic; no Lean file was read, imported, executed or re-certified by this lane. `rules/design-authority.md` authority order and `rules/git-concurrency.md` exact-lease/freeze rules remain binding. This is an authorized research proposal, not implementation authority.

## Current source equations

For receipt `r`, define `finish(r)` to clone all fields and set only `completed := true`. The eight other fields are `drain_index`, `incoming_relation`, `replay_ack`, `created_seed`, `selected_relation`, `origin_index`, `task`, and `cause`. Rust derives `Clone, Eq, PartialEq` for this exact structure (`C:108–120`). No field is replaced by a weaker relation-ID comparison.

The producer-side operation visible in this closure is `record_source_drain_completion` (`C:2284–2290`): successful `try_reserve(1)` appends `finish(r)`; reserve failure omits evidence and returns. It neither changes an Origin nor deduplicates equal completions. The actual enqueue-time attachment producer is outside the two-file R87 closure, so the pending attached prestate is an explicit hypothesis here. The visible seed appends an Origin with receipt `None` (`C:3848–3857`); formal attachment changes only `formal` (`3863–3874`). Frame initialization has receipt `None`, and transactional replacement clones the receipt unchanged (`2401–2429`). Checkpoint/rollback save and truncate Origin/completion frontiers separately (`2167–2168,2183,2271`). These operations provide no equation changing an existing attached pending bit to true.

Let `Q(i,o,q,p)` mean the actual indexed Origin has `o.occurrence=q` and `relation_pair(o.relation)=Some(p)`. Other Origins are skipped; **every** matching Origin participates, even one with a missing or malformed receipt. In particular, relation-ID equality does not collapse duplicate Origin occurrences.

| Actual reader | Exact receipt/selector behavior |
| --- | --- |
| `source_drain_completed`, `C:2292–2295` | `exists j, completions[j] = finish(r)`. Duplicate equal clones are accepted by this existential helper. |
| `checked_source_drain`, `C:2299–2340` | Whole-inventory selection. Accepts exactly one `Q` Origin with attached `r`, `r.origin_index=i`, `created_seed=selected_relation=o.relation`, exact supplied task and cause, supplied cause occurrence equal to `q`, and exactly one completion equal to `finish(r)`. Returns the attached pointer and completion index. It imposes no pending-bit requirement and no `incoming=None` / `replay_ack=None` requirement. Any malformed matching competitor, missing/duplicate completion, or second matching Origin rejects. |
| `checked_source_drain_in_cuts`, `C:3038–3092` | Checks cut ordering/end bounds. Same identity/task/cause equations within the two half-open index intervals, **plus `r.completed=false`**. Exactly one matching Origin and completion are required only inside those intervals. Returns the pending attached pointer and completion index. Competitors outside cuts are retained and do not affect this selector. |
| `checked_internal_use_root`, `C:3183–3217` | Scans **all** Origins for `Q`. Zero candidates gives `MissingUseRoot`; second candidate gives `AmbiguousUseRoot` before receipt checks. The unique candidate needs an attached receipt with `completed=true`, exact Origin index, `created_seed=selected_relation=o.relation`, incoming/ack both `None`, cause occurrence `q`, and task pair `p`. Any receipt failure gives `MissingUseRoot`. The completion vector is never read. It returns the attached receipt. |
| saved `internal_root_view_from`, receipt block `R:1897–1930` | Selects indexed Origin/receipt and checks Origin pointer, relation and HIR occurrence; requires pointer identity of the attached receipt with the saved `entry.source_drain`; checks saved index/created/selected/cause-HIR equations and `completed=true`. This function does **not itself** rescan matching Origins/completion clones or directly check incoming/ack absence. Its stronger construction history comes from live checked emission. Its separate route selector requires exactly one matching Internal route (`1883–1892`). |

The uncut and cut joins are different functions from the actual Internal helper. The proposed paired Internal reader below is also a different function; none of its extra predicates may be inserted into a correspondence theorem about the current saved reader.

## Current live-to-saved owner path

`ReceivingResidualExperiment::current_internal_emission` (`R:2622–2682`) authenticates the sole definition use and formal-permission incidence, reads the exact current physical effect lower slot, constructs slot-0 constraint occurrence and the value pair of the semantic Internal fact, and calls `State::checked_emission_for_internal_use`.

That checker (`C:3141–3179`) authenticates indexed emission/admission, current bound/readback/slot equations, entry owner and lower lane, exactly one emission for the physical slot, admission relation and bound relation pair. It calls the global attached-only root helper, then `require_relation_ancestry`. The returned `CheckedBoundEmission` retains `use_root`, `use_origin_index`, `use_origin` and `use_source_drain` (`C:641–653`). No completion index or completion pointer is carried.

The wrapper `CurrentInternalEmission` preserves this evidence and the exact source root pair (`R:201–206`). `ProviderEntryCertificate` and `ProviderNativeContextProjection` retain it (`210–214,5039–5075`). `InventoryPackage::capture` then copies it into `InventoryEntryRequest` (`4801–4819`), whose source evidence fields are only the Origin index/pointer and attached receipt pointer (`582–595`). `InventoryInternalRootView` returns those same fields (`1161–1183,1943–1964`). Package construction calls `internal_root_view()` before succeeding (`5036`). Consequently changing only the live helper would still leave the saved completed-bit guard, and changing only the saved guard would leave live construction unavailable for a pending receipt.

The native owner inventories already retain all Origins, all attached option shapes and all indexed completions (`R:3739–3806`). Owner round trips check exact order, indices, lengths and pointer identity (`3855–3896`; generic helper `5458–5471`). Package capture copies all three inventories (`4943–4964,5006–5016`). Thus the data required to authenticate a completion at the saved boundary already exists; no filtered Origin inventory or synthetic completed Origin is needed.

The separate saved publication verifier (`R:3978–4020`) demonstrates the eight-field comparison: it validates pending attached evidence and a selected completed clone, including both indices and every non-completion field. Its uniqueness comes from cut-reader construction, rather than a fresh global uniqueness scan in that verifier. This is a correspondence pattern, not an Internal-global certificate that can be reused unchanged.

## One candidate proposal: a borrowed, sealed Internal receipt pair

**Candidate only:** define one private-field carrier in the context owner, tentatively `CheckedInternalSourceDrain<'a>`, containing the borrowed owner State, Origin index and pointer, attached receipt pointer, completion index and completion pointer. Provide sibling-readable accessors. Only the context checker constructs this carrier. A saved package copies the carrier by value while borrowing the same immutable owner; siblings cannot forge its private fields. Existing tests beneath the context module are not an independent seal or production theorem.

The live constructor must first preserve the current **global** `Q` scan and its `MissingUseRoot` / `AmbiguousUseRoot` distinction. It then checks the current index/seed/selected/incoming/ack/cause/task-pair equations, requires the attached receipt to be pending, and scans the **whole** completion vector for exactly one `finish(attachment)`. Missing, malformed or duplicate completion evidence makes the observation unavailable. It returns both physical records and the exact completion index. This is an Internal-specific constructor: it must not introduce the generic publication reader's external exact-cause/task arguments or use a cut window to discharge global uniqueness.

The carrier follows one coherent path:

`InternalUseRootEvidence -> CheckedBoundEmission -> CurrentInternalEmission -> ProviderEntryCertificate -> InventoryEntryRequest -> InventoryInternalRootView`.

Keep the existing physical emission/admission/current-slot checks and final ancestry check. Replace the loose root receipt fields in this **candidate path** with the paired carrier, or retain redundant fields only with explicit equality checks. Preserve the source root pair and original full constraint occurrence; the saved path currently compares only the HIR projection in several places, so it must not reconstruct a different slot to validate the pair.

At saved consumption, validate the same carrier against the complete borrowed package: owner State pointer equal to `live_state`; indexed Origin equal to the retained Origin pointer; attached option present and pointer-equal to the carrier attachment; indexed completion present with owner index and pointer equal to the carrier completion; attachment pending; completion completed; and completion equal to `finish(attachment)` across all eight fields. Return that pair. Do not set a pending bit on a copy, replace the Origin's attached record, or call the completion clone the original attachment.

Global selection uniqueness can be transported by this sealed carrier plus the immutable owner borrow and exact complete owner round trips; it need not be recomputed by another global search at every saved consumption. If the integration cannot establish that the carrier was constructed by the designated checker and still borrows the same owner snapshot, it must rescan the full matching Origin/completion sets or reject. Private fields, lifetime discipline and snapshot identity are **candidate implementation obligations**, not properties of today's public `CheckedBoundEmission` fields. The candidate cannot claim uniqueness solely from an indexed successful lookup.

The completion scan adds O(number of completions) work to the existing O(number of Origins) live root selection and O(1) carrier storage. The saved selected-record checks add no inventory allocation and no new global traversal beyond current owner round trips. Deep Rust receipt equality costs are additional; no timing or bound on nested cause data was measured. Completion reserve omission and rollback remain legitimate missing-evidence cases; do not turn observational unavailability into a new ordinary-inference requirement.

## Exact claim boundary and minimized discriminators

Under explicit hypotheses of one unique global `Q` Origin, valid direct-root index/seed/selected/cause/task-pair fields, and all other consumer guards being satisfied:

1. Let attachment be pending `r`, and completion inventory be the singleton `[finish(r)]`. The proposed pair constructor accepts and returns distinct attached/completion records. The current Internal helper rejects at `!receipt.completed`; its current saved receipt guard also rejects the pending pointer. One Origin and one completion suffice.
2. Let attachment already be completed and completion inventory be empty. The current Internal helper's receipt test can pass; the proposed pending-plus-completion constructor rejects. This shows the candidate is **not** an equivalence-preserving refactor of the current private reader's arbitrary-state branch behavior. It is a proposed reader contract with different evidence requirements.
3. Duplicate the singleton completion. The candidate must reject duplicate equality matches even when both records have the same fields and relation ID; `source_drain_completed` alone would accept. Add a second `Q` Origin, even sharing the same relation ID, and the candidate must return global ambiguity before selecting a convenient receipt. An Origin outside a publication cut still competes in this global Internal scan.

These are conditional branch derivations, not generated or executed compiler fixtures. The actual producer attachment call and full reachable-state invariant are outside R87's source-read scope. No Rust/Lean theorem or source-generated execution follows from the examples.

Under the unchanged attached-completed Root premise declared by the contract, the candidate still cannot supply `Origin.source_drain_receipt.completed=true` while preserving that Origin and its pending attachment. The returned completed clone proves a statement about a second record. Changing that pointer/field in the mathematical inventory, dropping a competitor, or treating the pair as the original Root would require an unproved interface change. Exact owner: primary/proof lane must establish a new justified projection/application while keeping unchanged R57/R84 definitions, or adjudicate a separate design gate. This proposal therefore supplies **no safe production slice or Root closure under the present grant**. That blocker does not invalidate the source-local paired transport proposal as research.

Current-reader correspondence remains useful independently: the proof lane can prove the actual uncut/cut/attached/saved branch relations separately. R86's failed declarations and reduction diagnostics establish none of those theorems. This source report does not import or certify them.

## Checks, coverage and resources

Commands: read-only `cat` of contract/manifests/amendment; Python 3 standard-library SHA-256/byte checks; whole-file `rg -n` over exactly C and R for receipt types/APIs, root evidence structs, completion and attached field accesses, constructors and live/saved caller transport; focused `sed` reads of all cited owners; `date -u`. Some broad tool output was truncated, then relevant owner blocks were read directly. The coverage claim is whole-file search over 557,779 source bytes, not a line-by-line audit of unrelated solver code or whole-crate transition exhaustiveness.

Oracle independence: conclusions come from pinned Rust branches and pointer/data transport, not a checker that assumes a supplied transition model. The examples share Rust `Clone`/`Eq` behavior and explicitly stated prestate/other-guard hypotheses. No executable experiment, seed/range enumeration or mutation run occurred; the named duplicate/competitor cases are proposed falsifiers for future separately authorized verification.

No source paths outside C/R were read in R87. No Rust, Git, test/build/compiler/Lake/Cargo/formatter command, scratch/cache/target/environment/worktree creation, nested CLI, child agent or external service was used. This note is the only write. CPU and peak RSS were not measured. The source wall cap is 1000 seconds without reset; first timestamp `2026-10-31T14:03:54Z`, corrected-pin resumption `14:05:59Z`, with the intervening stop included in elapsed accounting. Final timestamp and frozen artifact SHA are returned with submission.

Recommended next action: fresh source/compiler review of this single paired-carrier proposal and of the proof lane's **current-reader** relations, preserving the precise Root application blocker before any Rust implementation admission.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/effect-permission-native-drain-reader-r87-source.md` only.
- Baseline: `9931800b1aed04402049a0e7685630f24b9e5e56`; corrected admission supplied by primary at `d6cbc700c`.
- Changed dependency pins: corrected contract hash `2ec7f33760b4ef8cdb3ac434dcf415f473a2019f4acf87c25786f77e0fc81261`; r2 manifest `e3d1b0590ea1fb179cc89039665b04d0d4d9bd2ec6a63290df4f90011fe2be96` supersedes `c96e2ada0461e0ed5527af4c4d96e697034aa9428420f56c10b6d489825409f4`. Both source hashes remain unchanged as listed above.
- Review/claim status: candidate owner-local transport proposal plus bounded source equations and conditional discriminators; independent review pending; no implementation, theorem acceptance, Root or production closure.
- Checks already run: contract/source hash/size checks, two-file whole-file symbol/caller inventory and direct owner reads. No tests/builds.
- Proposed research-checkpoint message: `research: propose paired Internal drain evidence transport for R87`.
- Shared-record deltas left to primary/curator: STOPPED/FROZEN and this note's hash; current-versus-proposed reader distinction; pending Root application and snapshot-seal obligations; corrected pin provenance. No shared task/index/authority/question-bundle files were changed.
