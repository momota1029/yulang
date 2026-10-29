# R20 Rust handoff — ordinary native-prefix probe

- **Sprint / revision:** `EFFECT-PERMISSION-NATIVE-PREFIX/20261030-r20`, contract revision 2
- **Contract SHA-256:** `49dc3bacbff9a536deaee6a45c0fe808ee7010c3eef4a73bb4b1a7d3019b822e`
- **Amendment 01 SHA-256:** `203152e8f91f13091d02ed08558c479e9ac09cb7f655d7949828e11331a8cc72`
- **Inputs manifest revision 2 SHA-256:** `ef67605cf9ed126de83d1cd434bee8afe2d86b43c38d6d2dcb31538fcb5150f4`
- **Assignment / handoff revision:** `/root/effect_permission_native_prefix_r20_rust`, revision 1
- **Parent:** original inference/executor soundness, effect hygiene, principality, termination and source/native obligations; all remain OPEN.
- **Baseline:** `871de7c6dca9c2645ad10bad231f05c46392b244`; R19 Rust source inputs were reused only as owner-path guidance, not as evidence of the R20 runtime call.
- **Role / worker:** implementer, `/root/effect_permission_native_prefix_r20_rust`; current-session launch acknowledged by Luna. No descendants.
- **Requested / observed runtime:** `gpt-6-luna` / `high`; observed model and effort UNKNOWN because no effective-runtime metadata was exposed.
- **Exact modified source paths:**
  - `isolated/ep-native-r20/project/crates/yu-solver/src/candidate_effect.rs` — `8d1603f91ec0f582fb0b4616f42d11eb51e87b1524bd58d3a4cb6b88eee37230`
  - `isolated/ep-native-r20/project/crates/yu-solver/src/candidate_scheme.rs` — `3fda40d2f6403022c9c49546e27599b87c0c9aaee0f0e5f70dd3e86e96e9f199`
  - `isolated/ep-native-r20/project/crates/yu-solver/src/candidate_source.rs` — `28a988aed00d2c203c287553cd71c77a5f4cf3a90c79ee63aa0439238351fc12`
  - `isolated/ep-native-r20/project/crates/yu-solver/src/lib.rs` — `c5b4fbde290dd36c5fa3818df7bffeea9dece1dc8370c50298a6651049420dc4`
  - `isolated/ep-native-r20/project/crates/yu-solver/src/term.rs` — `59282832b5972b919f0c790193732f8be2a6a464dcf742d6e07ba084e469d32c`
- **Receipt:** `isolated/ep-native-r20/project/receipts/native-prefix-receipt.json`, SHA-256 `fa0b472bd0ce7477f8d082872439da3158e7f2d2c0fe92e9a46cc40a598e4e27`. It retains exact Cargo argv, complete captured stdout/stderr, exit status, resource measurements, input identities, the attempted test source, and the explicit no-runtime-trace result.

## Result and source/native correspondence

Outcome class: **provisional test-only instrumentation; runtime probe blocked before execution**.

I added reversible `#[cfg(test)]` trace hooks for graph-plan items and SCC members, source roots and actions, formal annotation entry, session and term-arena journal transitions, tuple children and the selected `intern_structure` owner stages. The intended ordinary module was `my provider x = x; my selected (x: (int, bool)) = provider x`, with the selected formal annotation as the positive scalar-tuple path. The one Cargo command failed while compiling the test binary, so this source module, SCC prefix, selected occurrence, journals and native call were **not executed or authenticated**. No parent/source/native correspondence was established.

The source owner path follows R19's inspected route: `InferenceSession::execute` → `execute_scc_plan` → `execute_candidate_graph_plan` → `execute_candidate_source_root` → scheduled `FormalAnnotation` → `candidate_formal_annotation` → `with_term_events(positive_tuple)` → `intern_structure`. R19's conditional source handoff did not provide the actual R20 SCC/member/provider trace or the same-call native tuple observations; it was rejected for those missing edges. R18's exact `TupleInput` shape was inspected and the amendment's phase-indexed observed/skipped/unavailable contract is followed. Since the test never ran, every `TupleInput` field is recorded unavailable in the receipt; no defaults or successful stand-ins are supplied.

## Check and blocker

One serialized command only:

`cargo test --locked --offline -p yu-solver --features shadow-apply-candidate --lib r20_native_prefix_selected_ordinary_candidate_trace -- --nocapture`

Result: exit 101 after 40.613 seconds; no test output and no trace marker. Available RAM before launch was 28,706,570,240 bytes; process CPU affinity was one CPU; sampled peak process-tree RSS was 45,875,200 bytes; the address-space cap was 2 GiB and timeout 180 seconds. The exact raw streams are in the JSON receipt. No Cargo retry was made.

The first compiler diagnostics identified two R20-local instrumentation mistakes (`SourceAnnotation.text` does not exist; `RoutePurpose` has no `Debug`); both were corrected in the owned files after the sole Cargo invocation and remain unverified. The detached test build also reports two `E0063` failures in **unleased** `crates/yu-solver/src/shadow_apply.rs`: its `Graph` initializers lack `formal_capture_trace_id`, which is present in the detached `candidate_scheme.rs` dependency. Detached `shadow_apply.rs` SHA-256 is `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`; the main-tree copy is `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`. I did not modify this file or request an expanded lease.

**First missing source edge:** test-binary compilation did not reach runtime; after the two local diagnostics are fixed, the unleased `candidate_scheme::Graph.formal_capture_trace_id` → `shadow_apply.rs` initializer edge still prevents this probe from launching. The exact compiler errors and hashes are in the receipt.

## Premises, TODOs and next step

- R20's selected native-prefix evidence, journal-owner event trace and selected invocation identity remain OPEN.
- R18 `TupleInput` application remains OPEN. The missing output is not an observed/skipped runtime classification: the test did not run at all.
- Original inference/executor soundness, effects, principality, termination, native correspondence and production remain OPEN. No semantics, source domain, expected output or diagnostics were changed.
- **TODO `R20-RUST-BUILD-EDGE-1`, owner Luna:** reconcile the detached `Graph` field/initializer dependency at its owning lease or isolate a coherent immutable revision. Inputs: this receipt's full E0063 diagnostics and the two hashes above. Falsifier: a pinned build still fails the two `shadow_apply.rs` initializers or any changed dependency hash is unauthenticated. Any further Cargo probe requires a new explicit assignment/resource authorization; this assignment's single Cargo attempt is spent.
- **TODO `R20-RUST-TRACE-1`, owner Rust source lane after build-edge resolution:** run the selected ordinary source module and authenticate every plan/action prefix and both journal owners; record every R18 field as observed, skipped, or unavailable through return/failure. Falsifier: missing/reordered event, unclassified action/writer, unmatched transaction token, occurrence/arena mismatch, or unsupported field value.
- **TODO `R20-LEAN-APPLICATION-1`, owner Lean lane:** do not treat this handoff as a trace premise. Keep the call-specific application theorem OPEN without an executed trace; any later proof must consume only a frozen source-native receipt.
- **Next related in-envelope step:** none available to this writer under the spent one-command allowance and exact current dependency state; Luna must resolve the unleased build edge before a successor probe.

## Budget, files and writer stop

- Assignment grant: 900 seconds. Measured Cargo wall time: 40.613 seconds. Other active time was not instrumented precisely; no fabricated remaining-time claim is made. One Cargo attempt consumed; zero Lean audits, zero Astra work, zero descendants.
- Coverage achieved: source owner-path inspection, exact R18 field inventory, test-only hook implementation, and raw bounded Cargo failure receipt. Coverage not achieved: test execution, plan prefix, journal transitions at the selected call, native input fields, trace-to-Lean interpretation.
- Writes stopped: **yes**. No other worker files, manifests, lockfiles, current state, Git data, or main-tree paths were changed.
- New output paths: `isolated/ep-native-r20/project/receipts/native-prefix-receipt.json`; `tasks/agent-loop/inbox/effect-permission-native-prefix-r20-rust.md`.
- Known disposable scratch: `isolated/ep-native-r20/project/build-target/` (the explicitly leased Cargo cache). The `receipts/` directory was created for its exact leased JSON file. No other scratch path was created.
- Pending independent review: not assigned; these bytes are not self-certified.
