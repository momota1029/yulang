# I15: known-partition SCC qualification regression

- **Request ID:** `20261016-loop-a-implementation-value-scc-partition-020`
- **Revision:** 1
- **Owner:** Luna primary
- **Branch/baseline:** `research/simple-sub-intrusion`, `62f72243ab7980826b4631d56aa7849f4a2fe2cc` (post-A21 pushed boundary).
- **Scope:** One `cfg(test)` addition to `crates/yu-solver/src/candidate_value_graph.rs`; no production graph/SCC/identity/accounting code or test expectations changed.
- **Source before:** SHA-256 `d08f6c5fb9ae4c5f005b6cb40aa3462f4f58b350cd6842b76a15d2dfdb520bec`.
- **Frozen source:** SHA-256 `b3f52bbc7b386103b3b39045ab5845a016694ec2279fcb59a255167449c8a2bd`.

## Regression

The new `candidate_value_graph::scc_tests::sealed_partition_controls_qualification` fixture builds eight anonymous internal vertices with matching forward/reverse adjacency. It adds the selected cycle, duplicate edge, one-way bridges, disconnected vertex and self-loop through `Graph::edge`:

`(0,1),(1,2),(2,0),(0,1),(2,3),(3,4),(4,3),(4,6),(6,7),(7,6),(5,5)`.

The independently known partition is `{0,1,2}`, `{3,4}`, `{5}`, `{6,7}`. The test creates associations for all 64 ordered endpoint pairs, seals the graph, and asserts `qualifies` exactly when each pair lies in the same expected set. It then calls `seal` again without mutation and verifies all classifications remain unchanged. It does not pin numeric SCC representatives or infer expected results from a second independent call to `seal`.

This checks the existing Value-reference SCC qualification kernel only. It does not establish source-event adjacency, typed-source adequacy, soundness, principality, Simple-sub/F5 migration or production readiness.

## Read-only pins

- `crates/yu-solver/tests/candidate_intrusion_observation.rs` — `04a876b9fe0a3a45f2d1996446a11d0b36dce3bb26ad02537118e4853e4b78e1`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` — `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `tools/inference-playground/src/runtime/program.rs` — `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748`

## Verification

Two commands ran serially, one Cargo process at a time, `CARGO_BUILD_JOBS=2`, 180-second timeout each:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_value_graph::scc_tests::sealed_partition_controls_qualification -- --exact --test-threads=1` — exit 0; 1 passed, 713 filtered.
2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --test candidate_intrusion_observation -- --test-threads=1` — exit 0; 3 passed, 0 failed.

`git diff --check -- crates/yu-solver/src/candidate_value_graph.rs` passed. No other tests, builds, benchmarks or timing samples. One bounded M1 compiler-referee review remains pending before integration.
