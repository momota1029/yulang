# R86 source lane — two-record join and attached-root interface

Sprint `NATIVE-RECEIPT-JOIN/20261031-R86`; assignment `/root/r86_source`; handoff revision 1.
Outcome: **source-native-evidence / bounded source characterization**, pending fresh independent review.
Worker state: **STOPPED**; this revision is frozen on submission; no descendants or other outputs.

## Objective, authority and dependencies

Inventory every receipt/Origin/completion transition in the original seven admitted Rust files, inspect the exact initialization/rollback dependencies in the two Amendment 01 files, and distinguish the publication join from both Internal root consumers. This is source inspection with an explicit field derivation, not a Rust execution, extracted semantics proof, or A/B closure.

Contract: `tasks/agent-loop/sprints/native-receipt-join-20261031-r86.md`, SHA-256 `fbba407ea6a59e2a0856a369e8e8ea815766c3e241460fe3ea84fa493343453b`.
Initial manifest: `tasks/agent-loop/sprints/native-receipt-join-20261031-r86-inputs.json`, SHA-256 `e94dfb586a42052073620809ec17936c9c78e3025e017a1ffedea89c2df8debc`. Amendment 01: `tasks/agent-loop/history/native-receipt-join-20261031-r86-amendment-01.md`, SHA-256 `7c83569391ab2ec87d81365d87681dcc3366189bb1acc0e3015be52d0521c9b5`, committed/pushed per primary at `799cfef81` before the new source reads. Amended manifest SHA-256: `511553a67c35cd9c9adf90230eae422f8418a12ffe952fb5223266a6f76d0377`. Its two duplicated navigation entries in `source_search.result_paths` / `source_lane.reads` were reported to the primary; each added file is pinned once in `inputs`, and this worker counted/read each once.
Pinned source baseline: `a44adf1f2fda99f896debf11b5f58c207728b030`; primary-supplied admission commit: `d07c1ca90`. No Git command was run by this worker.

Governing scope: R86 “Fixed outcomes and falsifiers”, “Exact lanes and artifact leases”, and “Budget and execution gate”; `rules/design-authority.md` authority order; `rules/git-concurrency.md` disjoint-file/frozen-review rules; `rules/research-lab.md` and its preserved source-evidence distinction; root operating map and sprint skill child-packet/handoff rules. The accepted original A/B quantifiers, source domain, effect hygiene and birth-level qualification remain premises owned by the primary/proof lane. No language interpretation or new production decision is proposed here. No Lean input was read or checked in this source-only assignment.

| Pinned Rust input | Bytes | SHA-256 at initial and final inspection |
| --- | ---: | --- |
| `crates/yu-solver/src/candidate_context.rs` | 265778 | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/lib.rs` | 1660759 | `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df` |
| `crates/yu-solver/src/candidate_receiver.rs` | 292001 | `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` |
| `crates/yu-solver/src/candidate_scheme.rs` | 509269 | `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631` |
| `crates/yu-solver/src/shadow_apply.rs` | 276524 | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |
| `crates/yu-solver/src/shadow_apply/local_source_observation.rs` | 126363 | `fa7e5a1288eae3ed9093a733645adcac4bd88011802d4fe95fdd10acab2fe66b` |
| `crates/yu-solver/src/candidate_native_inventory_tests.rs` | 21440 | `6b3670e5548ad0000c4717949476a3a3038b2e06490f7f58ed4c6a1ac522d638` |
| `crates/yu-solver/src/candidate_intrusion.rs` (Amendment 01 restricted scope) | 31786 | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` (Amendment 01 restricted scope) | 354102 | `75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909` |

## Decisive result and exact premise

There are three relevant reader contracts. `checked_source_drain` joins two records over the entire inventory. The used publication reader, `checked_source_drain_in_cuts`, joins two records inside saved intervals and requires the attached record to be pending. `checked_internal_use_root` reads only the attached record and requires it to be completed. The saved Internal inventory consumer also requires that same attached record, by pointer identity, to be completed.

Consequently the exact two-record projection is source-supported, but it does **not** supply the attached-completed premise of either Internal root consumer. The first failed field equation for a producer-created attached receipt is `attached.completed = false`, while the consumers require `attached.completed = true`. This is a possible R86 interface no-go under the unchanged consumer definitions, not a proposed repair or proof of the original Root. Cut-local uniqueness is a separate limitation: it does not establish whole-inventory uniqueness when competitors outside the cut are retained.

## Producer, replacement, rollback and completion inventory

Abbreviations below: `C` = `candidate_context.rs`, `L` = `lib.rs`, `R` = `candidate_receiver.rs`, `S` = `candidate_scheme.rs`, `A` = `shadow_apply.rs`, `O` = `shadow_apply/local_source_observation.rs`, `T` = `candidate_native_inventory_tests.rs`. Line numbers refer to the pinned bytes above.

The receipt type (`C:109–120`) derives `Clone, Eq, PartialEq`. Let

`fields(r) = (drain_index, incoming_relation, replay_ack, created_seed, selected_relation, origin_index, task, cause)`

and `finish(r)` be a clone with `completed := true`. Equality of receipts checks all eight fields and the completion bit; cause and task use their actual Rust equality, not an invented numerical surrogate.

| Transition / owner | Exact visible behavior |
| --- | --- |
| State initialization, `C:1005–1006,1053–1056,1065` | `State` derives `Default`; its Origin, completion and typed-drain vectors therefore default to empty for an actual `State::default()` construction. `source_drain_completions` is a private field; Origins and typed drains are `pub(super)`. Amendment 01 closes the whole graph default/initialize chain below. |
| Source seed, `C:3848–3857` | Reserve one Origin, then append `{ relation, occurrence.clone(), inferred_entry, formal: None, source_drain_receipt: None }`. No deduplication of Origins by relation ID occurs. |
| Formal attachment, `C:3863–3874` | `candidate_context_seed_with_formal` first calls the seed owner, then changes only the last Origin's `formal` when supplied; debug assertions check its relation/occurrence. Existing inferred-entry evidence is retained. This does not change receipt/completion data. |
| Drain initialization, `C:2401–2411` | `begin_typed_drain` reserves and appends a frame whose receipt is `None`; index is the previous drain length. |
| Successful enqueue attribution, `L:14272–14318` | `start_typed_drain` records pre-seed `origin_index = origins.len()` and `incoming_relation = item.relation`, calls seed-with-formal, sets selected item relation to `incoming.or(seed)`, then calls `enqueue_item`. Only after enqueue succeeds, if seed and selected relation exist and the frame is present, constructs the sole explicit receipt literal: `completed:false`, exact index/incoming/ack/created seed/selected relation/task/cause. The frame gets a clone. The indexed Origin gets the original only if its relation equals created seed, its occurrence equals the supplied occurrence, and its receipt is `None`. This never overwrites an existing attached receipt. |
| Frame transactional replacement, `C:2414–2429` | With a transaction and no prior undo for that index, prepares replacement acknowledgement storage; copies every frame field, including `source_drain_receipt.clone()`, replaces the live frame, and puts the original frame in undo. Receipt values are equal before/after replacement; no Origin or completion is changed. Earlier reserve/lookup errors return before replacement. |
| Terminal completion, `L:14967–15032` | Requires top frame, terminal stage, ordered acknowledgement cursors, and all acknowledgements completed at `ReturnReady`. Fallible preparation/acknowledgement work precedes completion append. At final return, optional replay return is retained, then the frame receipt is cloned and passed to `record_source_drain_completion`; the frame is popped and previous processing restored. The Origin is not mutated. |
| Completion vector write, `C:2284–2290` | `try_reserve(1)` failure silently omits observational evidence. Otherwise append `finish(receipt)`. Thus `fields(C_new) = fields(receipt)` and `C_new.completed = true`. No uniqueness check is performed by this writer; a caller can append the same clone twice. The terminal path consumes the frame, but this inventory does not infer a global exactly-once theorem for every sibling caller. |
| Checkpoint, `C:2149–2180` | Stores separate Origin and completion lengths (`2167–2168`) and drain/undo lengths (`2175–2176`), together with the other state frontiers. |
| Rollback, `C:2182–2272` | First truncate completions to saved length (`2183`); restore eligible saved drain frames, by assignment or push, then truncate drains (`2191–2200`); finally truncate Origins to their saved length (`2271`). Pre-existing attached receipts have no undo write because this producer attaches only to its newly appended seed. |
| Commit cleanup, `C:2361–2370` | Truncates typed-drain undo and resets acknowledgement preparation state on retained frames; no attached receipt or completion mutation. |
| Error cleanup, `L:14252–14265,14334–14343`; `C:4593–4600` | Synchronous failure pops/truncates newly owned drain frames and restores processing; these local bodies do not remove Origins or append completions. Outer transaction rollback is a separate owner. The older drain branch in `L:14082–14115` is bypassed by the early `run_candidate_typed_drain` return when a candidate graph exists, and does not attach a receipt itself. |
| Whole owner replacement, `S:2456–2479` | `start_candidate_graph` constructs `GraphState::default()`, calls `state.intrusion.effect_algebra.initialize()` (`2458`), sets context `scoped_enabled`, conditionally replaces `scope_inventory`, reserves/resizes `graphs` by definition count and `locals` by source-local count, reserves/populates `local_captures`, calls `refresh_bytes`, then assigns `self.candidate_graph = Some(state)` (`2478`). This assignment replaces the entire previous graph, including both receipt owners; it does not selectively transport old Origins or completions. Amendment 01 establishes that the fresh successful replacement has empty Origins, completions and typed drains; all earlier `?` failures leave the old optional graph unassigned by this body. |
| Session initialization / final transfer, `L:10124–10126,20303–20309` | A new session begins with `candidate_graph: None`; finalization moves the entire optional candidate graph into frozen inference data. This is a move of both owners, not an attached-receipt completion write. |

No other explicit Origin initializer, attached receipt write, completion append/truncate, or whole graph replacement was found in the admitted seven files. Nonreceipt `origins` variables in F5 capture and unrelated `completed` variables were inspected as search false positives. Size accounting references subtract receipt storage at `C:2438,2440,2666,2733,2735,2772`; they do not mutate receipts.

Rollback does not imply that every retained Origin always has a completion. Conditional frontier witness: immediately before a checkpoint let one Origin already carry pending `r` and let completion length be zero; append `finish(r)` after that checkpoint, then roll back. The shown code retains that Origin, removes its post-checkpoint completion, and restores eligible drain undo. This is a pending state, not proof of incorrect acceptance or of a concrete full solver execution. A successful terminal step can also lack a completion after observational reserve failure. Whole owner replacement resets the owner as a unit; it supplies no equation completing an old attached record.

## Exact readers, rejection and uniqueness

Define `qualifies(i,o,q,p)` as `o.occurrence == q` and `relation_pair(o.relation) == Some(p)`. Invalid/other relation pairs are skipped. This predicate includes every matching Origin regardless of cause, receipt availability, inferred-entry evidence or formal evidence; those competitors must not be filtered away.

### Complete-inventory join: `C:2292–2340`

`source_drain_completed(r)` returns `completions.contains(finish(r))`; it is existential and accepts duplicate equal records.

`checked_source_drain(q,c,t)` accepts exactly when there is exactly one qualifying Origin in the whole vector for `p=task_pair(t)`, and that Origin has receipt `r` satisfying:

- `r.origin_index = i`, `r.created_seed = o.relation = r.selected_relation`;
- `r.task = t`, `r.cause = c`, and `c.occurrence() = q`;
- exactly one indexed completion equals `finish(r)` in the whole completion vector.

It returns `{origin_index:i, completion_index:j, relation:o.relation, receipt:&r}`. The returned receipt is the **attached** record, including its original completion bit. It never returns a pointer to `completions[j]`. It does not require `r.completed = false`, `incoming_relation = None`, or `replay_ack = None`. No qualifying Origin, missing receipt, failed field check, missing completion, duplicate equal completions, or second qualifying Origin returns `None`. A malformed matching competitor rejects rather than being discarded. There is no call to this uncut API in the admitted seven files.

### Cut publication join: `C:3038–3092`; capture at `R:3418–3464,3553–3562`

`capture_native_call_cut` saves Origin/completion/emission lengths before the call. The later publication capture saves end lengths and invokes `checked_source_drain_in_cuts` on `[origin_cut,origin_end)` and `[completion_cut,completion_end)`.

The reader rejects reversed cuts or ends beyond owner lengths. Inside those intervals its conditions are the complete-inventory join conditions above, with two differences: it explicitly rejects `r.completed = true`, and completion existence/uniqueness and Origin uniqueness are checked only inside the supplied intervals. It does not call `source_drain_completed`; the filtered iterator directly checks exact clone equality. Matching rows outside those intervals remain unexamined competitors for this selector. It returns the same pending attached pointer plus the unique matching completion index. Capture stores an owned clone of that pending receipt in `ResidualPublicationObservation.source_drain`, alongside both cut/end pairs and indices.

### Saved publication verification: `R:3978–4020`

`OwnedResidualProjection::verify_call_records` rejects Origin/completion indices outside their saved intervals and reversed emission cut/end. It requires indexed Origin, attached receipt, parallel borrowed receipt, selected completion, and relation to exist. It checks Origin index/relation/occurrence; pointer equality of borrowed receipt to the attached receipt; full equality of attached receipt to the saved pending clone; exact receipt Origin index; pending bit; exact effect task and original fact cause; completion index and completed bit; and equality of **all eight** non-completion fields between completion and attached receipt. It also checks relation index and live relation-pair round trip. Its subsequent native-bound branch additionally checks physical slot/emission ownership, bound equations and relevant emission uniqueness (`4021–4109`).

This saved verifier does **not** independently rescan matching Origins or duplicate matching completion clones. Nor does its receipt block recheck `created_seed = selected_relation = origin.relation`; that check belongs to capture's cut reader. Its stronger provenance comes from private construction through that reader and the owner round trips; it is not a standalone arbitrary-record selector with all of capture's rejection properties. No duplicate-accepting runtime execution has been established here.

### Checked Internal root: `C:3141–3217`; caller `R:2622–2682`

`current_internal_emission` reads the exact live physical effect slot, constructs slot-0 Internal occurrence and a value task pair from the semantic Internal fact, then calls `checked_emission_for_internal_use`. That method rejects missing emission/admission, bound/readback/current mismatch, wrong entry owner/lane, any physical slot with emission count other than one, missing relation, or foreign bound relation pair. It then calls `checked_internal_use_root` and requires relation ancestry (`C:3172–3173`).

The root reader scans **all** Origins for occurrence/pair and rejects a second candidate with `AmbiguousUseRoot`, even if relation IDs coincide. Zero candidates or no attached receipt gives `MissingUseRoot`. A unique attached receipt must satisfy:

`r.completed = true; r.origin_index = i; r.created_seed = o.relation = r.selected_relation; incoming_relation = None; replay_ack = None; r.cause.occurrence() = use_occurrence; task_pair(r.task) = use_pair`.

Any failed conjunct gives `MissingUseRoot`. It never reads the completion vector. The returned `InternalUseRootEvidence.source_drain` points to the attached receipt, and `CheckedBoundEmission.use_source_drain` preserves it. An attached completed record would not need a separate completion clone for this method to accept. This differs from both join readers.

### Saved Internal inventory root: `R:1796–1963,4801–4819`

`InventoryPackage::capture` takes `provider.provider.internal.emission`, constructs `InventoryEntryRequest` using its `use_origin`, `use_origin_index`, `use_root`, and `use_source_drain`, and copies complete native inventories. `internal_root_view_from` resolves the indexed Origin and its attached receipt (`1897–1898`). In the receipt/root block (`1917–1930`) it requires pointer identity with that retained Origin and with `entry.source_drain`, Origin/root relation and occurrence equality, receipt index/created/selected/cause equations, and `entry.source_drain.completed = true`. It also validates unique Internal route (`1883–1892`), indexed relation pairs, emissions/admissions, permissions, registration and plan/root correspondence. It neither looks up a completion clone nor calls the publication join. Thus the pending record returned by that join cannot replace this pointer-equal completed attached record.

## Inventory completeness, visibility and remaining readers

`Origin` and all its fields are `pub(super)` (`C:407–414`); `TypedDrainFrame` and `SourceDrainReceipt` are `pub(super)` and their fields are public (`C:85–120`). The `State` Origin/drain vectors are `pub(super)` (`1053,1065`); completion vector is private (`1056`). The completion writer, existential reader, join readers and borrowed completion enumerator are `pub(super)` methods. The Internal root helper itself is private; `checked_emission_for_internal_use` exposes its checked evidence to sibling code. `lib.rs:210–236` declares these sibling modules under the candidate feature. This visibility permits sibling access beyond the admitted closure; it is not a language-level seal proving all native writes enumerated.

`OwnedResidualProjection::capture` (`R:3739–3807`) collects **all** Origins with their owner indices, all optional attached receipts, and all completions without qualification filtering. `collect_owned_borrowed_inventory` (`2242–2256`) rejects index gaps and allocation failures. `verify_owner_round_trips` (`3809–3896`) checks exact pointer/index/order/length agreement with every live inventory; attached option shapes and receipt pointers must match. `borrowed_inventory_matches` (`5458–5471`) requires the iterator to end exactly with the captured inventory. `InventoryPackage::capture` (`4943–4964,5006–5016`) copies these entire Origin/receipt/completion inventories; it does not delete competing Origins to make the Internal selector unique. Full retention does not turn cut-local uniqueness into global uniqueness.

Other receipt readers in the closure:

- `S:1761–1774`: capture scans all slot-4 Origins, uses existential `source_drain_completed`, and caches/deduplicates relation IDs in a separate `completed_lambda_effect_origins` vector. This cache is not the Origin inventory and does not prove Origin uniqueness.
- `A:1053–1069`: `source_drain_receipts` scans all Origins, skips missing/uncompleted evidence, then checks exact Origin index/created seed/cause occurrence and `selected = incoming.unwrap_or(created)`; malformed completed attribution yields `ArtifactMismatch`. It does not reject duplicate equal completions. `source_origin_attribution` (`1071–1100`) rechecks identity equations and emits attribution from the attached record, falling back to occurrence-only evidence on failure.
- `A:2142–2157,2211–2243`: observation paths use that map, preserve qualifying source Origins up to the explicit cap, and mark incomplete/truncated coverage. `A:2393–2438` uses existential completion for forwarding consumer attribution, excludes replay/incoming records, checks selected/created equality and provider reachability, then requires exactly one consumer relation. These are separate source observations, not Internal root completion writes.
- `O:85–98`: local-provider observation uses the same map; `O:290–344,443–446` are diagnostic/test-source reads of attached receipts and existential completion. No receipt/vector mutation occurs there.
- `T:25–26,190–191`: the test-only adapter borrows raw Origin and completion slices; it adds no receipt completion proof or production transition. `C:4780–4785` declares two test children. Only `candidate_native_inventory_tests.rs` was admitted/read; `candidate_context_tests.rs` is outside the closure.
- `C:126,652,669` and `R:387,431–432,591,1180,1259,1269` retain receipt references, optional reference vectors, or the saved clone type described above. They are storage declarations, not writes to an attached Origin.

## Smallest field obstruction and coverage limit

Conditional source derivation: choose one unique qualifying direct Origin `o` at index `i`, with valid relation pair, occurrence/task/cause and all root identity equations; assume successful enqueue attribution and successful completion-vector reserve. The producer attaches `r` with `r.completed=false`. Terminal completion gives vector `[finish(r)]` while retaining exactly that `o` and its attached `r`. For these receipt conditions the join succeeds and returns `&r` plus index zero. The checked Internal root rejects with `MissingUseRoot` at `!receipt.completed`. Its saved consumer independently rejects the same pending attached pointer. One Origin and one completion are sufficient for this field mismatch; no competing Origin or duplicate clone is needed. This is a minimized interface witness under stated receipt/reader hypotheses, not a tested complete compiler fixture.

Separate competitor witness: put one matching Origin outside an otherwise valid cut and one inside it. The cut reader can accept the inside candidate while preserving both records; the full root reader rejects as ambiguous. R57 relation-ID uniqueness cannot be substituted for this occurrence/pair cardinality property, and this source lane assumes neither kind of uniqueness globally.

### Amendment 01: exact default/initialization and rollback dependency

These two initially external owners were inspected only after the primary reported committed/pushed admission `799cfef81`. Let `I` = `candidate_intrusion.rs` and `E` = `candidate_effect.rs`.

- `S:5–7` derives default for GraphState with `intrusion: candidate_intrusion::State`; `I:9–11` derives default with `effect_algebra: candidate_effect::State`; `E:297–299` derives default with `context: candidate_context::State`; `C:1005–1006` derives default with empty Origin, completion and drain vectors. This is the actual nested default chain, not an assumed initializer contract.
- `E:651–660` `initialize` writes only `self.brand` from atomic `NEXT_BRAND.fetch_update` with `checked_add(1)` and returns `Ok(())`; overflow returns availability error before publication by `S:2478`. It does not change the context. The rest of the admitted graph initializer does not modify the three vectors. Thus successful fresh graph replacement starts all three empty, while wholesale replacement removes the old owner as a unit.
- Checkpoint chain: `L:9489` puts `state.intrusion.begin()` in the route journal; `I:177–179` stores `effect_algebra.checkpoint()`; `E:661–663` stores `context.checkpoint()`. Rollback chain: `L:9746` calls intrusion rollback; `I:201–202` calls effect-algebra rollback on its exact saved checkpoint; `E:688–689` calls context rollback on its exact saved checkpoint before other effect-algebra restoration. That reaches `C:2182–2272` and its separate Origin/completion frontiers. No wrapper substitutes a different context checkpoint or writes either vector afterward.
- Success cleanup chain: `L:9577–9580` calls `context.commit_replay_operations(undo.effect_algebra.context_checkpoint())`, with accessor `E:515–517`; this is the already inspected `C:2361` cleanup, not a completion rewrite.
- In the two added files the exact receipt-symbol search has zero matches. The defaults/initialize/rollback/replacement and direct-context dependency searches found no direct Origin/typed-drain/receipt/completion vector write and no whole-context replacement. `I.completed` (`I:24`) is a relation-to-generation map restored at `I:237–243`; `E.origins` (`E:316`) is a private bound-to-task-pairs map restored at `E:701–707`. Neither is the source receipt completion/Origin owner. Their similarly named undo rows do not change this packet's equations.

The named initializer/rollback dependency seams are therefore closed as source text within the amended scope. The public Origin/frame fields and `pub(super)` helpers still allow uninspected sibling callers, and the two added files were read only for the amendment's restricted dependency scope. Test children `candidate_context_tests.rs` and `candidate_intrusion_tests.rs` remain outside admission. No assertion of whole-crate transition exhaustiveness follows. No further external initializer or rollback owner is needed for the exact chains above.

## Commands, oracle independence and resources

Read-only commands used: `rg --files` for instruction/contract locations; `cat`/`sed` for rules, sprint metadata and the admitted source excerpts; whole-file `rg -n` over the exact seven original Rust paths for the named source-drain APIs, Origin/frame access, initializers, mutable access, `mem::{take,replace,swap}`, whole graph assignment/default/move, checkpoint/rollback, completion-bit assignments, and module/test declarations; restricted dependency searches over the two Amendment 01 files; Python 3 standard-library in-memory SHA-256/byte/line inventories; `date -u`. The initial `python` hash command failed because `python` is absent; the same read-only task completed with `python3`.

This inspection covers all 3,152,134 bytes of the seven files by whole-file symbol/mutation search, with selected surrounding owners read for every relevant mutation and reader. Line counts: C 4785; L 36688; R 5795; S 8509; A 5577; O 1879; T 343. The exact expanded receipt-symbol search

`source_drain_receipt|source_drain_completions|checked_internal_use_root|owned_projection_source_drain|SourceDrainReceipt|checked_source_drain|source_drain_completed`

returned 85 matching lines: C 39, L 5, R 14, S 2, A 8, O 15, T 2. The additional mutation/whole-owner queries above address writes whose spelling omits those symbols. No randomized search, seed, bounded solver enumeration or mutation execution was used. No Rust/compiler/test/build/Cargo/Lake/formatter, Git command, environment/worktree creation, generated/scratch/cache/target output, or external service was used. Existing test source is source evidence only.

The evidence oracle is the pinned Rust text, independent of a toy checker that assumes the claimed transition rules. The field derivation shares Rust `Clone`/`Eq` semantics and the explicitly stated successful-path/prestate hypotheses; it does not independently establish those runtime hypotheses, Rust memory execution, full source extraction, or Lean correspondence. There is no independent review claim. Source hash drift, an unadmitted writer, a new semantic premise, resource exhaustion or scope expansion would invalidate/stop this packet.

Budget: one lightweight shell/Python process at a time; no heavyweight work or child agents. Source wall cap 1000 seconds; precise launch elapsed, total tool CPU and peak RSS were not measured by this worker. Initial authenticated hash timestamp was `2026-10-31T13:36:33Z`; at amendment entry `13:42:51Z`, 378 seconds had elapsed from that timestamp. A conservative 120-second startup allowance gave 498 seconds spent / 502 remaining at entry; the primary owns the actual launch receipt. The amendment adds no reset and has a 300-second subcap. New source inspection completed at `13:43:18Z`, 27 seconds after amendment entry, followed by handoff editing/revalidation within the same cap. Final timestamp and frozen note hash are returned to the primary in the submission message.

Recommended next action: have the fresh R86 reviewer compare the proof's exact projection against these distinct selectors and adjudicate the attached-bit and cut-versus-global interface obstruction before accepting an R84/Root application.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-source.md` only.
- Baseline: source `a44adf1f2fda99f896debf11b5f58c207728b030`; admission `d07c1ca90` supplied by primary.
- Dependency hashes changed: the primary-authorized amended manifest replaces initial `e94dfb586a42052073620809ec17936c9c78e3025e017a1ffedea89c2df8debc` with `511553a67c35cd9c9adf90230eae422f8418a12ffe952fb5223266a6f76d0377` and adds Amendment 01 plus two pinned source dependencies above. No source byte hash or base contract hash changed.
- Claim/review: bounded source-native evidence and conditional minimized interface witness; fresh independent review pending; no theorem/production closure.
- Checks already run: read-only hash/byte/line checks, seven-file symbol/mutation/caller/visibility inventory and two-file restricted initializer/rollback/default inspection; no tests or builds.
- Proposed one-line research-checkpoint message: `research: inventory R86 receipt join and attached-root mismatch`.
- Shared-record deltas left to primary/curator: record source lane STOPPED/FROZEN and this artifact hash; preserve distinct whole/cut join and attached-only Internal readers; retain all competitors, mark the exact initialization/rollback chains source-inspected under Amendment 01, preserve broader sibling closure limits, and adjudicate any R84 application with proof/review evidence. No shared state/index/authority/question bundle was edited.
