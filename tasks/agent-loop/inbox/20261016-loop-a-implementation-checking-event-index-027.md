# I19 native checking-event index implementation receipt

- **Request ID:** `20261016-loop-a-implementation-checking-event-index-027`
- **Revision:** 1 (frozen)
- **From:** implementer `/root/i19_checking_event_index`
- **To:** Luna primary, for dispatcher intake
- **Baseline:** `8efe58aee42962ce8eaaed84648d094ece9917fe`; editable input hashes matched the I19 packet before editing. Read-only dependencies and principles hashes also matched before verification.
- **Governing gate/invariant:** I19, local native `Graph::observed_checking` observation-index optimization under top-level inference principles §2. Preserve authentic checking identity, event ordinal/order, forward-map overwrite semantics, fallible reservation, no-allocation observation, and checked retained-capacity accounting. No propagation, admission, SCC, language, API, or F5 change.
- **Requested runtime:** Luna/high implementation floor. **Observed runtime settings:** UNKNOWN (runtime did not expose them).

## Reused and adapted prior work

- Reused the existing `Graph::retain_source` Apply traversal as the sole event and authentic `ConstraintOccurrenceId` constructor, the unchanged `checking` forward map, and the established `Graph::bytes` checked-capacity model.
- Reused the existing `conditional_reference_tests::fixture`, which takes the last binding's local-source carrier, and the earlier I15 retained Value/SCC regression structure. Adapted this test to compare each indexed lookup against a literal inverse scan of the original forward map, including after authentic repeated registration overwrites its entry.
- Adapted the prior `CandidateIntrusionObservation::events` complexity comment to reflect indexed checking lookup while retaining the Value descriptor scan cost.
- No earlier checking-event reverse-index implementation was found in the owner-path history. The prior event identity/order construction was retained; no superseded Simple-sub bypass or event fabrication was recreated. No earlier construction was rejected or withdrawn for this scope.

## Implementation

Changed only:

1. `crates/yu-solver/src/candidate_value_graph.rs`
   - Added private `checking_by_event: Vec<ConstraintOccurrenceId>`.
   - Fallibly reserves the index alongside the existing event vector and forward map before association registration. Constructs the authentic occurrence once, clones it into the unchanged forward map, and pushes that same identity at the old event count before appending the existing `Association`.
   - `observed_checking` bounds-checks the index and returns its identity only while the forward map still maps that exact identity to that event ordinal. It performs no fallback scan.
   - Counts checked `capacity * size_of::<ConstraintOccurrenceId>()` bytes. The existing source plan consumes `Graph::bytes`; the Arc-backed occurrence clone shares its payload and no payload charge was duplicated.
   - Added exactly `checking_event_lookup_matches_forward_index`, covering nonempty event storage, vector/event length, every ordinal plus out-of-range lookup, repeated authentic retention and forward-map overwrite, and the exact vector capacity-byte delta. The test takes/restores the vector only during the bytes comparison.
2. `crates/yu-solver/src/shadow_apply.rs`
   - Updated only the `CandidateIntrusionObservation::events` complexity comment. It states expected O(1) checking lookup per event with O(E) collision worst case, expected full iteration O(E*V+E), worst O(E*(V+E)), and no allocation.
3. This frozen receipt.

Static cost: the index adds O(E) fixed-size identity elements, with amortized vector reserve work. Identity clones share the existing Arc-backed occurrence payload. Each event lookup uses an expected constant-time HashMap access; `observed_value` still scans the Value map. No benchmark or runtime measurement was performed.

## Verification

The three packet commands ran serially with `CARGO_BUILD_JOBS=2`, each under `timeout 180s`, one test thread, and no additional suite/check/benchmark:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_value_graph::conditional_reference_tests::checking_event_lookup_matches_forward_index -- --exact --test-threads=1` — exit 0; 1 passed, 0 failed, 715 filtered.
2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --test candidate_intrusion_observation -- --test-threads=1` — exit 0; 3 passed, 0 failed.
3. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli intrusion_expression_calls_keep_original_spans_and_local_names -- --exact --test-threads=1` — exit 0; 1 passed, 0 failed, 22 filtered.

The tests establish this bounded lookup/overwrite/accounting behavior and the selected native/playground compatibility cases. They do not prove inference soundness, principality, source-global correspondence, or any open A/B, N1, F5, or production gate. HashMap collision worst-case behavior and allocation failure execution were not measured or induced. No broad suite, benchmark, or whole-workspace format/check ran.

## Handoff

Frozen Rust diff paths: `crates/yu-solver/src/candidate_value_graph.rs`, `crates/yu-solver/src/shadow_apply.rs`. Review is pending; this producer does not certify its own output. Luna should freeze/check the artifact hashes and submit it to the dispatcher, then follow the board's separately bounded R29 compiler-referee and R30 performance-auditor review packets. No Git operation was performed.
