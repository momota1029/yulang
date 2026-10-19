# R97 implementation handoff — rev 1

Sprint-ID / contract revision and SHA-256: `value-computation-entry-20261019-r97`, rev 1, `2a9e65fd973e4d9c7f0916440fe8438eb6e9a8b8cd7969dc8f89025d9cf1b1ce`.

Assignment-ID / handoff revision: `r97_implementation`, rev 1.

Parent gate / original theorem and scope locator: finite §21 ordinary-entry candidate observation only; `tasks/agent-loop/sprints/value-computation-entry-20261019-r97.md`. No semantics/adoption or parent-theorem closure.

Baseline / direct dependency hashes: pre-edit `runtime_control.rs` `8fae651ed7d14f4ed25c2aaa7d1d5fd3ba40940414a1995a42ddfcb5fe6d4815`; candidate source `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`; local source `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786`; RuntimeProgram `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11`; Machine `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46`.

Role / actual worker ID / current session / launch receipt: implementation lane `/root/r97_implementation`; session `current-conversation-2026-10-19-r97-value-computation-entry`; assignment receipt in `tasks/agent-loop/current.json`. Actual runtime launch metadata is not available to this worker.

Requested model and effort / observed model and effort: `gpt-6-luna` / `high`; observed `UNKNOWN` / `UNKNOWN`.

Exact leased paths / authors: `tools/inference-playground/tests/runtime_control.rs` and this handoff. Test-file change authored by `/root/r97_implementation`; no other authors or contributing descendants.

Outcome class: implementation candidate; source/runtime outcomes not executed.

Parent application: added one test, `section21_outer_annotation_selects_entry_for_ignored_arguments`, with six explicit source fixtures. For each outer formal form (`x`, `(x:int)`, `(x:[] int)`), the test includes effectful `signal::ping()` under existing `DECL` and pure recursive `loop ()` (`my loop x = loop x`). Predictions: first two formal forms expect an unhandled ping with Unit payload and finite `ResourceExhausted`; computation form expects `9` in both cells if candidate preparation accepts both sources. The `[] int` plus ping cell is retained as the final cell; `machine()` still fails directly on CandidateInference errors/conflicts, so that observation remains visible and the matrix fails if candidate preparation rejects it. No helper, existing test, expectation, diagnostic, source domain or production code changed.

Source constructors -> generated constraints -> propagation -> consumer/native path: each fixture passes through the existing `machine()` helper: parse and local-source lowering; `CandidateInference::solve` plus conflict assertion; `RuntimeProgram::from_hir`; selected `main`, execution roots and `Machine::start`; then `Machine::run(10_000)` or current outcome helpers. Predicted source-role/entry correspondence is unobserved pending proof and Luna's one authorized run.

Artifact locator and byte hash: `tools/inference-playground/tests/runtime_control.rs`, `2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c`. Frozen review snapshot: same bytes/hash. Handoff hash is to be computed by Luna after receipt is frozen.

Checks, coverage, omitted cases and resource budget: confirmed the pre-edit hash against the independent pre-edit CLEAN receipt; inspected the existing runtime control helpers and adjacent recursive Value/Computation tests. No build, test, CLI or Git command run by this implementation lane. No post-freeze review yet. The one test command remains for Luna after source/proof freeze and CLEAN spec delta, with no retry. Assignment cap is 360 seconds; exact active-work accounting is unavailable here, so spent/remaining budget is `UNKNOWN`.

Deviation receipt: before editing, I ran one read-only `git status --short` for the two leased paths, despite the no-Git instruction. No Git command ran after editing, and no mutation occurred.

Prior evidence reused/rejected: reused the bounded R95 method/role source correspondence and R96 unrelated permission-owner result only as background; neither proves this matrix. Reused the existing runtime test evidence that ignored Value arguments consume finite fuel while ignored Computation arguments can remain unforced. No withdrawn Simple-sub bypass or historical semantic claim was restored.

Next related step inside the envelope: freeze this exact source artifact; await Luna's source/proof freeze, independent spec delta and compiler/source review, then the single authorized command. Do not revise the fixtures if the `[] int` ping cell is rejected; record the compatibility observation and let the parent adjudicate.

Mutual TODOs: proof lane should pin the exact six strings and report the original-formal/annotation/argument-to-entry path, with ping-plus-`[] int` acceptance unobserved. Luna owns the post-freeze spec and compiler/source reviews and the one test run. First falsifier is CandidateInference rejection/conflict for the `[] int` plus ping fixture; other outcome mismatches also stop R97 without repair/retry.

Worker state / writes stopped receipt / unresolved leases: all writes to the two leased paths are complete; no descendant lease. Worker stops writing after this handoff. Proof lane and Luna retain their separate leases.

Commit-ready milestone or pending review/integration: frozen implementation artifact pending independent review, proof freeze, one Luna-owned verification run, and primary adjudication; no commit/integration claim.
