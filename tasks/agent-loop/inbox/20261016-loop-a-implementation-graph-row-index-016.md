Request-ID: LOOP-A-I12-ROW-INDEX-016
Revision: 1
From: implementer (primary `/root`, configured `gpt-6-luna` / high; observed runtime settings unknown)
To: next_action_selector
Parent-gate: I12 renderer row indexing; original Simple-sub/F5/source/theorem/production gates remain OPEN
Baseline: `7e1140c90b5743eb564b109d1fa4b88ae9b74c7b`; frozen inputs: `shadow_apply.rs` `e3290b31a9c49873b33fad48bddf0b3b5eb70f42bb62f26d9bec71c080f944e0`, `render.rs` `c3b3fe3000340f7891583f2208aba6d149a15c358ee9efbbb59d173f7e499ca6`, `candidate_scheme.rs` `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`, `candidate_intrusion.rs` `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c`, CLI test `4085d5e8f2c00a982419f236d92e58aa6d20fd469df6e1beeb6f35148aeaf8ea`
Kind: implementation
Claim/task: Index candidate graph rows using the existing canonical identity, without changing inference or observation behavior.
Missing-evidence: None for this bounded implementation packet; independent review and Luna integration remain pending.
Owners: `crates/yu-solver/src/shadow_apply.rs` `CandidateGraphRow::{same_identity, PartialEq, Eq, Hash}`; `tools/inference-playground/src/render.rs` `graph_into`.
Depends-on: I11 pushed at baseline; existing recursive graph CLI contract.
Scope: `CandidateGraphRow` equality/hash use graph-state address plus `intrusion.rep(row.key)`, preserving Value/Effect typing. Renderer keeps the ordered row vector and first representative/locality, with one local identity-to-index map. No solver union, path compression, inference-rule, rendering-order, charge, cap, error, or formatting changes intended.
Acceptance: focused identity/hash regression covers repeated and duplicate stored rows, typed namespaces, distinct states, and separate candidate solves; recursive graph output remains deterministic; fresh independent review required before integration.
Proposed-outputs: `crates/yu-solver/src/shadow_apply.rs`, `tools/inference-playground/src/render.rs`, this inbox receipt
Checks/resources: one serialized Cargo process at a time, `CARGO_BUILD_JOBS=2`, 180s timeout per command; native test `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --lib shadow_apply::tests::candidate_graph_row_hashing_matches_identity -- --exact --test-threads=1` → 1 passed, 712 filtered (test 0.01s; profile 19.53s); CLI test `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli recursive_graph_is_finite_and_deterministic -- --exact --test-threads=1` → 1 passed, 21 filtered (test 0.02s; profile 8.34s). `git diff --check` passed. No benchmark.
Prior-work: I11 `7e1140c90b5743eb564b109d1fa4b88ae9b74c7b` indexed graph nodes by its established pointer/index identity; row identity is different and uses state identity plus typed canonical representatives. Reused existing `same_identity`; did not infer a row key from raw ordinal or graph address.
Priority-reason: Removes the two remaining renderer row scans while retaining the already accepted output and observation contract; independent of blocked N1 and proof-dependent production gates.
Stop/escalate: Frozen source and receipt hashes are supplied to Luna/dispatcher. Stop on review finding or any discrepancy; repair only within these leases and rerun the assigned focused checks if needed. No production cutover or parent theorem closure.
