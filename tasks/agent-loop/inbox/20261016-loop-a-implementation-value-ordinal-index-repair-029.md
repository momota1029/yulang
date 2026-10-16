# I20-R1 implementation result — byte assertion repair

Packet: I20-R1, dispatcher-selected repair
Revision: 1 (frozen)
Baseline source hash: `f4733b984f7c7a93fb0cc6674b324a74bfd75d090d1156cf6d4ca952a77f5537`
Baseline shadow source hash (preserved): `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`
Baseline inbox028 hash (preserved): `301978e28da500913c5dafc4c8808bda7625a728f7b8a9a00c535532676036a5`
Requested role/model: implementer, Luna/high minimum
Observed runtime model/effort: UNKNOWN (runtime metadata unavailable)

## Authority and invariant

This is only the assigned test-assertion repair for the I20 internal value-ordinal lookup optimization. It follows top-level inference principles §2 and the existing `Graph::intern` identity/ordinal invariant. The reverse map contains one real semantic `Value` at each semantic ordinal and no auxiliary fragment entries. The assertion verifies only that `Graph::bytes()` loses the reverse table's capacity contribution while that table is temporarily taken and restored.

The copied Module payload counter is still charged on both sides: the test takes only `values_by_ordinal`, while `copied_module_payload_bytes` remains a field on `Graph` and is still included by `Graph::bytes()`. The separate assertion that this counter equals the sum of Module payload bytes in the semantic map remains unchanged. The delta assertion now compares against only `checked_capacity_bytes::<(usize, Value)>(values_by_ordinal.capacity(), ...)`; no observed byte count is hardcoded and production accounting is unchanged.

Original source theorem, F5, and production gates remain OPEN/BLOCKED. Test success does not prove inference correctness or close those gates.

## Prior evidence reused

- Preserved the implementation and rationale in frozen inbox 028, SHA-256 `301978e28da500913c5dafc4c8808bda7625a728f7b8a9a00c535532676036a5`.
- The preceding failed focused run measured a 504-byte delta while expecting 539; 504 was the map-capacity contribution and the 35-byte payload remained on both sides. This explains the isolated assertion correction.
- I19 commit `cb31b7b0d27cf9238616bb5927102812b2e792c9` remains the reused checked-reservation/index-construction precedent. I19's index and overwrite guard were not edited.
- No superseded Simple-sub bypass, inference path, graph identity, or API change was introduced.

## Exact repair

Only the `added_bytes` expression in the newly added `value_ordinal_lookup_matches_semantic_vertices` test changed in `crates/yu-solver/src/candidate_value_graph.rs`. It now measures reverse-map capacity bytes alone. All other I20 production code, complexity comment, test assertions, and inbox 028 are preserved byte-for-byte from the repair baseline.

## Verification

Ran the prescribed commands serially, stopping on failure or timeout. All passed:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_value_graph::conditional_reference_tests::value_ordinal_lookup_matches_semantic_vertices -- --exact --test-threads=1`
   - Exit 0; `1 passed; 0 failed`.
2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --test candidate_intrusion_observation -- --test-threads=1`
   - Exit 0; `3 passed; 0 failed`.
3. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli intrusion_expression_calls_keep_original_spans_and_local_names -- --exact --test-threads=1`
   - Exit 0; `1 passed; 0 failed`.

No additional suite, build, probe, benchmark, or measurement was run. Benchmark budget was 0 processes / 0 samples. No Git operation was performed.

## Frozen outputs and hashes

- `crates/yu-solver/src/candidate_value_graph.rs`: SHA-256 `8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50`
- `crates/yu-solver/src/shadow_apply.rs`: SHA-256 `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` (unchanged)
- `tasks/agent-loop/inbox/20261016-loop-a-implementation-value-ordinal-index-028.md`: SHA-256 `301978e28da500913c5dafc4c8808bda7625a728f7b8a9a00c535532676036a5` (unchanged)
- `tasks/agent-loop/inbox/20261016-loop-a-implementation-value-ordinal-index-repair-029.md`: this frozen result

## Scope and next handoff

Changed paths in this repair: the leased source file above and this exact inbox file only. No new proof TODO is indicated by this assertion repair. The original proof/F5/production gates and independent review remain outstanding; request the assigned independent review of the frozen I20 artifact, then Luna may adjudicate/integrate and consult the dispatcher for the next packet. No disposable files were created or identified for cleanup. Runtime model/effort remains UNKNOWN.
