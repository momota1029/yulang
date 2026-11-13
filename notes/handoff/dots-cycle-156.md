# dots cycle 156: actual terminal reserved run and journal-derived evidence

## Run / recovery
- Started 2026-11-13T03:27:19Z. Latest user limit: publication/report within55minutes (04:22:19Z).
- Fresh integration base `dfe5efd4b8f74b3a7fefd95ac6d129997c917ded`; standing orders/inbox reread, ACTIVE, Evidence/I-25 lane.
- Previous cycle155 completed. No overlapping writer was found. Current-cycle worker was interrupted after checkpoint `c1eac48b3fe3a5a3be5de566badf2cecf85262fc`; retained local source and logs recovered.
- Heartbeat gap: public timestamp remained03:36 until recovery. This does not satisfy uninterrupted ten-minute heartbeats; recovery records it rather than inventing missing heartbeats.
- Recovery isolated the retained caches and rebuilt all16 original new modules from final source bytes, rather than trusting stale shared artifacts. A final one-theorem catalog bridge was also compiled separately.
- Intermediate recovery checkpoint `0f2b725ad46492e0ba848985260d21293e01f725`: all15 changed files retrieved at the immutable commit and byte-compared.
- Only work/dots-main published. No frozen Audit.lean/README, spec, lakefile, or classifier/transition definitions changed.

## Results and scope (健全性 / 補助)
1. **任意の実到達状態の journal から request 履歴を復元（補助・健全性）**:
   For arbitrary roles/registry/root and a state reachable by actual Value steps, `safe_history` reconstructs Collected for the finite chronological catalog of emissions from syntactically variable-free packets. No final Supported, final model-validity, or executor hypothesis is supplied. Packets with variables are filtered, not proved sound by this result. Catalog membership gives sub-batch Supported and model validity.
2. **任意有限個の scalar 点引数（健全性）**:
   Current scalar Shape requires exact query/argument alignment, lower scalar observations without nominal descriptors, no input captures/names, and source definition. Under actual reachability and request provenance or safe-catalog membership, selected Instance follows. Arguments may share source identities. Recursive dictionary soundness still requires explicit coverage of every selected path; this is not unrestricted evidenceNode.
3. **元の root の非点 scalar 区間（健全性）**:
   For an arbitrary actual reachable state and every current model, initial root interval order is preserved backwards through actual Value model preservation. Exact locate reconstruction transfers it to current carrier endpoints. Current scalar Shape plus Supported requests yields selected Instance at the ORIGINAL root; no additional endpoint-order premise is assumed. The final `CatalogScalarIntervalRoot.selected_instance` replaces Supported with syntactic membership of every generated request in safeCatalog. It does not prove such coverage automatically or cover arbitrary newly emitted descendants.
4. **予約出力の実際の終端経路（具体的回帰・健全性）**:
   The concrete empty-journal fixture performs install → equality feedback → nominal refresh. At the final3-slot state every source is Known, all generated occurrences reduce to the root, equality is closed, point-closed nominal descriptors prevent reobservation, every enabled installation is Committed, and novel alias merge is impossible. All actual Value constructors are excluded: Stable is proved. Actual selected Classify, a positive current model, current Instance/Evidence and the exact completed diagnostic tree are proved. Any continuation from this endpoint is equal to it. This is one concrete run, not a general termination theorem.

## Acceptance / remaining obligations
- The reserved-output regression left open in155 is now terminal and stable.
- General request-history evidence no longer requires a manually supplied final provenance witness when catalog membership is available.
- **V5 remains8/14 open**: progress, execution, halted, whereAccessible, treeExecution, canonicalLocalOrder, evidenceNode, generatedChildren. No general field was closed by the concrete halted theorem.
- No completeness/principality result, universal executor, general saturation termination, or unrestricted scalar/nominal recursive coverage is claimed.
- Restrictions (variable-free emitted schema, current scalar Shape, selected-path catalog coverage, original-root interval invariant) are implementation proof boundaries, not new language rejection rules.

## Verification
- Retained focused build logs:754jobs (multiargument),771jobs (final classification/stability),774jobs (request history),772jobs (completed endpoint); successful in their respective scopes. Other interval-focused675/716jobs successful. These are not additive job counts and not full-build results.
- Recovery: all16 original new source modules rebuilt into an isolated cache with Lean4.35.0 `--trust=0`, exit0.
- Final catalog-root module compiled `--trust=0`, exit0.
- Seven explicit audit shards rerun, exit0;93 printed axiom records, only propext / Classical.choice / Quot.sound.
- New all-declarations dependency gate covers private/generated helpers as well; AXIOM-GATE-PASS:270declarations, exit0. All17 new modules are imported from Yulang.lean.
- `git diff --check` PASS. New-source scan: no sorry / new axiom / native_decide.
- Full `lake build`, root Audit.lean and `tools/verify-lean.sh` deliberately NOT run under standing orders; supervisor verification remains required.
- CI API for recovery checkpoint returned an empty run list; not a CI pass.
- Free space at recovery:39GiB. Start measurement was not recovered. Usage quota unknown.

## Yulang2 との照合
No new Yulang2 executable run in recovery; existing source semantics were used unchanged. Lower-only scalar inspection was checked against the existing Lean inspect definition. Runtime conformance beyond the existing fixture is unverified.

## Next1–3 bridges
1. Derive safe-catalog coverage for arbitrary selected reachable stable nodes instead of assuming membership.
2. Extend interval-order formation to genuinely generated children, keeping source identity/provenance explicit.
3. Handle variable-bearing named schemas/captures and connect the resulting general Evidence rule to V5.evidenceNode.

## Public theorem inventory
17new modules /92public theorem declarations. Group scopes above apply; exact quantifiers/types are in the linked Lean sources. The added single bridge is `GeneralDictionaryCatalogScalarIntervalRoot.selected_instance`.

### GeneralDictionaryCatalogEvidence
`structural`, `node_evidence`, `covered`, `dictionary_evidence`

### GeneralDictionaryCatalogMultiArgumentEvidence
`instance_of_history`, `instance_of_catalog`, `structural`, `covered`, `dictionary_evidence`

### GeneralDictionaryCollectedRequests
`reachable`, `supported`, `supported_subset`, `shape`, `models`

### GeneralDictionaryMultiArgumentCoverage
`selected_instance`, `root_dictionary_evidence`, `completed_tree_evidence`, `covered_of_previous`

### GeneralDictionaryMultiScalarExample
`checked`, `metadata`, `requests_empty`, `initial_source`, `reachable`, `actual_instance`, `inhabited_dictionary`

### GeneralDictionaryMultiScalarInspection
`inspect_exact`, `report_exact`, `point_checks`, `private_models`

### GeneralDictionaryProvenanceMultiScalarBranch
`branch_models`, `instance_of_shape`, `selected_instance`

### GeneralDictionaryReachableRequestHistory
`closed_before`, `administrative_packets`, `catalog_install`, `history_step`, `history`, `supported`, `eligible_closed`, `safeCatalog_install`, `safe_history_step`, `safe_history`, `safe_member`, `safe_models`

### GeneralDictionaryReservedCatalogEvidence
`catalog_exact`, `automatic_history`, `current_instance`, `current_evidence`, `no_initial_output_observation_needed`

### GeneralDictionaryReservedCollectedHistory
`installed_requests`, `installed_closed`, `installed_history`, `refreshed_history`, `refreshed_batch_models`, `nonvacuous_history`

### GeneralDictionaryReservedCompletedRun
`actual_stages`, `actual_path`, `initial`, `halted`, `continuation_eq`, `resolved`, `completed`, `resolves_iff`, `classify_iff`, `initial_terminal_sound_run`

### GeneralDictionaryReservedRefreshedClassification
`selected`, `decisions`, `value_selected`, `classified`

### GeneralDictionaryReservedRefreshedStability
`sources_exact`, `all_known`, `point_closed`, `no_reobservation`, `sites_exact`, `edges_empty`, `generated_only`, `raw_equal`, `equality_closed`, `installable_committed`, `stable`, `completed_reserved_run`

### GeneralDictionaryReachableRootIntervals
`root_intervals`, `locate_sources`, `located_intervals`

### GeneralDictionaryScalarIntervalInspection
`inspect_exact`, `report_exact`, `interval_checks`, `private_models`

### GeneralDictionaryProvenanceScalarIntervalRoot
`branch_models`, `instance_of_shape`, `selected_instance`

