# I20 implementation result — value ordinal index

Packet: I20, dispatcher-selected implementation slice
Revision: 1 (frozen)
Baseline: `cb31b7b0d27cf9238616bb5927102812b2e792c9`
Requested role/model: implementer, Luna/high minimum
Observed runtime model/effort: UNKNOWN (runtime metadata unavailable)

## Authority and gate

Selected authority: top-level inference principles §2, together with the existing `Graph::intern` identity/ordinal mapping and borrowed retained-observation contract. The edit is an internal observation lookup optimization and does not change inference semantics, language behavior, graph identity, or public API.

The original source theorem, F5, and production gates remain OPEN/BLOCKED. This implementation and its unit test do not establish those proofs or close those gates.

## Earlier work reused / adapted / rejected

- Reused the checked `try_reserve`-before-registration pattern from I19, commit `cb31b7b0d27cf9238616bb5927102812b2e792c9`, in `candidate_value_graph.rs`: reserve the reverse index for a new semantic vertex, while duplicate `intern` returns before reserving/cloning/accounting.
- Adapted I19's separate event-to-checking observation index to a `usize -> Value` map keyed only by semantic vertex ordinal. The map stores no auxiliary fragment entries and does not alter the I19 index or overwrite guard.
- Reused the existing `DefId::hash_eq_payload_bytes` owner accounting (`crates/yu-hir/src/module.rs`) for the copied `Value::Module` payload. `HirLocalId`, `HirParameterId`, `LocalSourceCatchBinderId`, and `HirOccurrenceId` carry shared HIR/source identities; no additional deeply-owned dynamic payload was found in the inspected Value variants.
- Rejected/refrained from all withdrawn Simple-sub bypasses. No inference route or theorem status was touched.

## Frozen changes

- `crates/yu-solver/src/candidate_value_graph.rs`: add `values_by_ordinal`, reserve it with the existing maps, clone a new semantic `Value` once into it, track copied Module payload bytes, use it in `observed_value`, include its table capacity and copied payload in `Graph::bytes`, and add the requested focused unit test.
- `crates/yu-solver/src/shadow_apply.rs`: only the `events` complexity comment changed. Descriptor lookup is expected O(1), collision worst O(V); iteration expected O(E), worst O(E*(V+E)); no allocation.
- `tasks/agent-loop/inbox/20261016-loop-a-implementation-value-ordinal-index-028.md`: this frozen result/TODO submission.

No tests were edited outside the selected source module. No manifest, lockfile, shared record, board, question, or other inbox was edited. No Git operation was performed.

## Verification and stop condition

Executed the first authorized check only:

```text
timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_value_graph::conditional_reference_tests::value_ordinal_lookup_matches_semantic_vertices -- --exact --test-threads=1
```

Result: **FAILED**, exit 101. The test reached the temporary take/restore byte measurement and observed `graph.bytes()` delta 504, while its expected value was 539. The 504-byte delta equals the measured `(usize, Value)` reverse-map capacity. The additional 35 bytes are the copied-module payload counter, which remains included in both `Graph::bytes()` measurements because the test temporarily removes only `values_by_ordinal`. The counter is separately compared against the sum of Module payloads. The assertion currently incorrectly includes that counter in the expected *delta*.

Per packet, stopped at the first failure. Checks 2 and 3 were not run. This failure is in the newly added test's byte-delta expectation; the code's observed delta matches the specified reverse-map capacity accounting. No change was made after this failure other than writing this frozen result inbox.

## Proposed follow-up TODO for dispatcher

Request-ID: `loop-a-impl-value-ordinal-index-028-r1`
Revision: 1
From: implementer; actual worker/runtime ID UNKNOWN
To: implementer
Parent-gate: I20 value ordinal observation-index implementation packet; top-level inference principles §2. Original source theorem/F5/production gates remain separately OPEN/BLOCKED.
Baseline: `cb31b7b0d27cf9238616bb5927102812b2e792c9`; input pins supplied by Luna: candidate_value_graph `2260658d2d9e961a4c7e1cb5a7dfeff35497452e26ea4b73b84d7b3e2134efc4`; shadow_apply `bd652ee34c3934bd39443178866c7be1afd05fd7abe7711883f899b6640bb21f`; candidate_source Plan `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`; solver identity helper `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`; yu-hir DefId/Arc owners `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e`; CatchBinder owner `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`; yu-syntax SourceNodeKey/GreenNode clone `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8`; native observation integration test `04a876b9fe0a3a45f2d1996446a11d0b36dce3bb26ad02537118e4853e4b78e1`; playground CLI test `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea`; principles §2 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
Kind: implementation
Claim/task: In the new unit test, verify only that temporarily removing `values_by_ordinal` subtracts exactly `checked_capacity_bytes::<(usize, Value)>(values_by_ordinal.capacity(), ...)` from `Graph::bytes()`. Keep the separate assertion that `copied_module_payload_bytes` equals the semantic Module payload sum; do not include that counter in the temporary-removal delta.
Missing evidence: focused test currently stops at a mistaken expected-delta assertion; the remaining prescribed integration checks have not run.
Owners: `crates/yu-solver/src/candidate_value_graph.rs` (`Graph::bytes`, `conditional_reference_tests::value_ordinal_lookup_matches_semantic_vertices`); `crates/yu-solver/src/shadow_apply.rs` (`CandidateIntrusionObservation::events` comment is frozen and need not change).
Depends-on: none for the assertion correction; preserve original theorem/F5/production gates as independent OPEN/BLOCKED dependencies.
Scope: repair only the byte-delta assertion in the exact source file and rerun the three serialized packet commands; no test expectation changes outside this new unit test, no semantic/API/architecture decision, no benchmark.
Acceptance: first focused unit test passes, then the two authorized integration tests return their expected 3/3 cases; confirm duplicate interning/accounting and all existing assertions remain intact. A test pass does not prove inference soundness or close original gates.
Proposed-outputs: `crates/yu-solver/src/candidate_value_graph.rs` and `tasks/agent-loop/inbox/<new dispatcher-assigned exact path>`; this worker's current lease is frozen.
Checks/resources: exact three commands and bounds from I20 packet; stop at first failure, 180s each, jobs=2, test threads=1; verification owner is Luna/dispatcher-selected implementer.
Prior-work: I19 commit `cb31b7b0d27cf9238616bb5927102812b2e792c9` supplies the checked event-index insertion pattern; this I20 test failure is a local accounting assertion mismatch, not evidence against the reverse-index invariant.
Priority-reason: correct the focused test's isolation of table-capacity accounting, then complete the approved bounded verification before review.
Stop/escalate: no semantic bottleneck observed. Do not escalate to Astra; stop if corrected focused test or either integration test fails.

## Complexity and limits

- Additional storage is O(V + I): the reverse hash table stores one `(usize, Value)` per semantic vertex, and `I` is the copied `DefId` payload bytes for Module Values. No raw-vertex-length holes are allocated.
- Population/cloning is O(V + I), plus amortized hash-table growth. `observed_value` is expected O(1), collision worst O(V). Event iteration is expected O(E), collision worst O(E*(V+E)); it allocates nothing.
- This is static accounting only. No benchmark was requested or run (budget: 0 processes / 0 samples); no speedup claim is made.
- Unverified: the two remaining prescribed checks, all broader tests, independent review, source theorem/F5/production gates, and runtime model identity.
