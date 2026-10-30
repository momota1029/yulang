# R51 independent review — FAIL pending B1 repair

Reviewer: `/root/r37_inventory_review`. Authors were confirmed frozen and STOPPED before review. This report is placed by the primary from the reviewer's returned report.

**BLOCKING B1 remains open.** The conditional Lean mathematics is internally consistent with its stated observations, but Rust observation instrumentation violates R51's failure-isolation requirement. No bounded acceptance or parent closure is granted.

## BLOCKING B1 — observation preparation can reject successful publication

Locations in `crates/yu-solver/src/candidate_receiver.rs`:

- `publish_authenticated_residual`: `complete_residual_plan(&pending)?`
- `complete_residual_plan`: new result-vector lookup, reservations and copies around lines 1174–1183
- `complete_residual_plan`: fallible publication-evidence planning around lines 1231–1246
- `residual_publication_plan`: observer-only slot/presence/emission checks around lines 1261–1319

The new prefix snapshots allocate with `try_reserve_exact(...).map_err(|_| native_unavailable())?`. These errors propagate before any Forward call. Publication-evidence planning errors also propagate as solver errors. Thus a previously successful private publication can fail solely because observation storage cannot be allocated or observation identity is unavailable. R50 reserved the decision plan but had neither these snapshots nor this observation-planning failure path. The finding is limited to added observation work, not pre-existing allocation for authenticated decisions.

This violates the contract: “Any missing identity or allocation-lost observation returns unavailable from the private query and cannot change ordinary inference success.” The objective also requires missing or ambiguous evidence to make only the partial observation unavailable.

The later `capture_native_publication` path correctly returns `Option`, with reservation failure producing `None` after successful forwarding. Prepublication observation preparation must have the same isolation.

**Minimum closure:** preserve R50's authenticated decision/publication behavior while making added observation preparation best-effort. Lost snapshot allocation or unavailable publication metadata must disable the private observation rather than propagate an error into publication. Freeze the repair and obtain focused independent delta review. No semantic or expected-output change is needed.

## Source publication checks

The actual Forward call preserves `decision.endpoint`, `pending.upper`, `pending.fact.id`, and `pending.fact.cause`. `checked_source_drain` checks source occurrence, task pair, origin index, created/selected relation, exact task and cause, cause occurrence and retained completion membership. Missing or duplicate evidence returns unavailable. The completion producer tolerates reservation failure, so completion-ledger pressure itself does not become a solver error; this does not close B1.

The capture path rereads physical result-row storage and requires unique endpoint membership. Newly emitted evidence checks matching slot/readback, owning admission, exact relation pair, emission past the retained frontier and ancestry from the selected forwarding drain.

AlreadyPresent is handled separately: it verifies the existing slot and unchanged emission count without attributing an old emission to the current decision. Zero prior emissions is accepted. Prefix/suffix checks preserve initial lower vectors and require exactly the planned new operands in lane-local order; independent row/atom cursors account for multiple appends. Unexplained appends or reordered slots make the observation unavailable.

Suppressed decisions issue no Forward call and do not remove existing native contributions. This supports local non-emission only, not global endpoint absence.

## Separate source-correspondence limits

The Lean model requires per-call publication/index identity, `originCut`, `emissionCut`, and pre-call observations. Rust retains one prepublication emission frontier and later selects a unique source drain by occurrence/task/cause; it does not retain the model's complete per-call record structure. Therefore full instantiation of `CallReads`, `DrainReads`, and `ModeReads` remains an explicit source-correspondence premise. The global frontier has not been shown equivalent to every model per-call cut.

This is not a claimed concrete runtime misattribution: no source-qualified path demonstrating one was constructed. Extraction completeness and execution remain open.

## Lean review and complete axiom census

All 24 declarations, theorem statements, proof bodies and Audit 8 printed types were inspected in `YulangClosure.NativeResidualPublicationR51`.

| Complete transitive axioms | Theorems |
|---|---|
| `propext` | `frame_preserves_existing`, `frame_preserves_same_family_sibling` |
| `propext`, `Quot.sound` | `accepted_plan`, `accepted_item`, `forward_exact_arguments`, `forward_current_native`, `new_emission_attributed`, `already_present_no_new_emission`, `forward_completed_drain`, `absent_completion_unavailable`, `suppressed_emits_no_local_call`, `unmatched_trace_count`, `accepted_forward_native`, `original_unmatched_survives_native`, `concrete_new_and_existing_publication`, `concrete_completion_loss_is_observation_gap`, `concrete_suppression_is_not_global_absence`, `concrete_bad_publication_observations_rejected`, `map_succ_nodup`, `range_nodup_constructive`, `accepted_index_order`, `accepted_item_at_index`, `accepted_index_unique`, `accepted_exact_native_frame` |

No final `Classical.choice`, `sorryAx`, project axiom or native-evaluation assumption appears. The theorems distinguish new emission from AlreadyPresent, preserve exact Forward arguments and causes, preserve initial contributions and same-family siblings, and limit suppression to absence of the indexed local call. Finite witnesses do not establish Rust execution or resource-failure behavior. In particular, `concrete_completion_loss_is_observation_gap` does not prove Rust ordinary-success preservation and cannot discharge B1.

## Frozen hashes and audit evidence

| Artifact | SHA-256 |
|---|---|
| R51 contract | `1cdaa9c5b6becf635e0bd859c7739d8122468fb92a688662ae6b78462803ae37` |
| `candidate_receiver.rs` | `e6d26028928fa6cfb77ece862f45a6391d813e5141ffe797d706ec2a44565d53` |
| `candidate_context.rs` | `c26a152e957980fcc844b7ff7145f712c4fd218b03415c50263e3dd81156c71f` |
| Rust handoff | `d0290a56f069856f6b5fc2288940a0f0b08c189423bd130d39ae35c2f2ed32d9` |
| R51 Lean | `78a729b25e95812ba292c4e625ec69e46ff5eb70ff3ac2ae5b85dd1b33214d61` |
| Proof handoff | `03cbddc0c57924b34b764ffb170c79b75d4cbeb55c1796bbdb245587f5710abd` |

The read-only `lib.rs`, R50 model/review/outcome and six source files in Audit 8's source-hash inventory match their recorded hashes. Audit 8 records input `3fe1232d184cd88b294735fc7faa32179bc372e8bfd12fffeaab2b1281e775f7`, stdout `fd0dee96c77683957c6a4d64b093eba88827a7d7fe2ff5931983f2e8be3a3377`, exit 0, empty stderr, Lean 4.35.0, one CPU, `-j1 -M1024`, and a 120-second timeout. Printed types and axiom census were checked, and source hashes reproduced. The recorded raw stdout hash was not independently reconstructed from the Markdown-fenced capture in this review; framing normalization remains unverified.

## Adjudication boundary and STOP

B1 blocks acceptance of the frozen Rust artifact under the unchanged R51 contract. Source-correspondence limits are separate from this concrete failure-isolation defect. Rust compilation/execution, complete extraction, per-call observation correspondence, Catch authorization, full subtraction/hygiene, original A/B, soundness, principality, termination and production remain OPEN.

Reviewer **STOPPED**. No files written by reviewer, commits, source edits, checker/compiler/build/test reruns, Cargo/Lake/formatter, scratch/cache/target/environment/worktree creation, descendants or persistent processes. No quarantined path was accessed or released. Primary owns placement and hashing of this report.

---

# R51 B1 delta review — PASS

Reviewer: `/root/r37_inventory_review`. Repair author explicitly STOPPED.

**B1 is CLOSED. No remaining blocker was identified in this focused delta.**

At `candidate_receiver.rs:941`, authenticated decision planning remains fallible and fail-closed. Its source classification and suppression checks remain at lines 1167–1229.

Observation preparation is separate:

- Lines 942–943 call `prepare_native_publication` without propagating an error.
- Lines 1233–1267 return `Option`; snapshot reservations, metadata allocation, missing identities and overflow disable observation with `None`.
- Lines 1271–1329 likewise return `None` for unavailable publication evidence.
- Lines 959–962 capture observations after forwarding through `and_then`. Capture failure cannot change the method's `Ok(())`.

The Forward loop at lines 946–956 retains decision order and exact endpoint, `pending.upper`, original fact ID and cause. Only authenticated-plan failures, inherited outcomes allocation, and actual forwarding failures remain on its error path. The outcomes reservation at line 945 is inherited core publication behavior, not an added observation reservation.

Verified hashes:

| Artifact | SHA-256 |
|---|---|
| Repaired receiver | `41272bf276761cdfe847264b4aaf0093d9feab361ca8d80881fd69ca86d449e0` |
| Rust handoff revision 2 | `c34b93de832899ad5e6f4a9a34ef1b50d7414adedcddd087a511caf3aa3bf7e3` |
| Unchanged context | `c26a152e957980fcc844b7ff7145f712c4fd218b03415c50263e3dd81156c71f` |

This PASS closes B1's direct error-propagation defect. Earlier source-correspondence limits, raw audit-stdout checksum authentication, execution, extraction completeness, parent A/B and production boundaries remain unchanged.

Reviewer **STOPPED**. Read-only inspection and hashing only; no writes, builds, tests, checker/compiler reruns, Cargo/Lake, descendants or persistent processes.
