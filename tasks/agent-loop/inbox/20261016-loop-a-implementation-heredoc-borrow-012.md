Request-ID: 20261016-loop-a-implementation-heredoc-borrow-012
Revision: 1
From: next_action_selector / resident_dispatcher_loop_a; implementation executed by Luna primary
To: next_action_selector
Parent-gate: I8 runtime literal-decoding allocation removal; original Simple-sub/F5 proof, source/runtime correspondence, and production parents remain OPEN separately.
Baseline: `1d298c18d661b22a034c64d9f32b376161747188`; direct source and authority pins are recorded in the frozen dispatcher packet.
Kind: implementation
Claim/task: Preserve admitted normal and heredoc string decoding while borrowing the leading quote delimiter instead of allocating a repeated delimiter string.
Missing-evidence: This local runtime test and source inspection do not prove source/runtime correspondence, whole-runtime correctness, inference behavior, or Simple-sub/F5 production readiness.
Owners: `tools/inference-playground/src/runtime/literal.rs::string` and its private unit tests; unchanged integration consumer is `tools/inference-playground/tests/runtime.rs::normal_and_heredoc_strings_decode_escapes_before_display`.
Depends-on: Existing frozen literal-decoding contract and runtime regression. No source grammar, decoding behavior, public API, or inference change.
Scope: Exact runtime literal file plus this unique receipt. Replace the owned quote repeat with the borrowed all-ASCII quote prefix; add one unit test for counts 3/4/8, Unicode plus escaped newline, an insufficient closing delimiter, and ordinary empty-string decoding. No parser, solver, feature, docs, or semantic edits.
Acceptance: Frozen source diff and hashes; both exact focused Cargo tests pass sequentially; one independent bounded M1 compiler-referee review; primary integrates exact authorized paths. This demonstrates only preserved behavior for the listed decoder cases.
Proposed-outputs: `tools/inference-playground/src/runtime/literal.rs` and this unique inbox receipt. Dispatcher owns `tasks/agent-loop/board.md`.
Inputs: `tools/inference-playground/src/runtime/literal.rs` baseline SHA-256 `8dfd2538070a3854c7a56dd8631bcae94999011bb8134cee7e71fb6a32ae46a1`; `tools/inference-playground/tests/runtime.rs` SHA-256 `2a263b532a1db0fceafb2787e5783461b3a6684f5a7a74c45995943ec2060e90`; README SHA-256 `59af7c1fd429f7c71d5a9c5bb3c6660519b18164329650cd32caaef784b6c1e6`; audited `crates/yu-solver/src/shadow_apply.rs` SHA-256 `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba`.
Checks/resources: Sequential, one Cargo process at a time, `CARGO_BUILD_JOBS=2`, test threads 1, timeout 180 seconds each, packet <=20 minutes. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --lib runtime::literal::tests::heredoc_delimiter_borrow_preserves_decoding -- --exact --test-threads=1` => exit 0, 1 passed, 13 filtered. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime normal_and_heredoc_strings_decode_escapes_before_display -- --exact --test-threads=1` => exit 0, 1 passed, 16 filtered. `git diff --check` => exit 0. No benchmark or broader suite.
Expected cost: Leading quote scan remains O(quotes). The owned delimiter repeat and O(quotes) temporary allocation are removed; the slice reuses the input bytes. No timing or overall speedup claim.
Stop/escalate: Any pin/lease mismatch, decoding difference, failed discovery, timeout, or semantic boundary requires stop. Preserve all existing expectations.

Result: The borrowed delimiter and local regression are implemented. Both focused tests pass. Independent review, shared-record synchronization, commit and push remain pending.
