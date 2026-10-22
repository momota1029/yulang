# Sprint R325 — execute exact candidate-selected member FieldTails

Status: RESULT_UNREVIEWED; unchanged Types runs through exact candidate-selected member/operator/import roots and captures the authoritative host-write payload. This is a bounded implementation result, not a proof or R149 closure.
Baseline: `d1603fc5dac7fd0db34984d18dc8d413396ea9e2` on `research/simple-sub-intrusion`.
Authority: the unchanged user goal, Authoritative R149, inference top-level principles, and the converted Japanese unified design/proof companion. No sample rewrite, expected-output change, type-directed behavior weakening, or arbitrary runtime member selection. User explicitly requires solo work; this is a degraded serial sprint with no independent reviewer or prover execution.
Dispatch: `next_action_selector` cannot be called without a subagent in the available tool surface, and the user prohibits subagents. Record this degraded route; do not simulate a worker.

## Parent and bounded outcome

The parent remains all unchanged Yulang2 playground samples passing through ordinary inference and execution with the actual R149 outputs, plus implementation proofs. R324 established successful experimental candidate inference for the unchanged Types source. The next exact consumer gap is `RuntimeProgram::from_hir`, which rejects every `LocalSourceForm::FieldTail` before execution.

Carry only successful, exact candidate dispatch evidence into runtime. Preserve the source root and occurrence of each active FieldTail, the exact selected `SourceMemberRootId`, receiver-first method application, and ordinary explicit method parameters. Compile only source member roots present in the same candidate HIR world and authenticated by the successful candidate. Missing, duplicate, ambiguous, or mismatched routes must leave runtime unavailable; runtime value shape must not select an implementation. Do not imply that this establishes the source/native bridge, principality, or the parent theorem.

Success for this packet: a bounded source-to-runtime path compiles exact selected member sources, consumes authenticated dispatch receipts, resolves exact imported definitions, and captures the actual `out::write` payload while resuming its saved continuation once. The unchanged Types source returns `(42, Yulang)\n`. Keep R149, Console, the broader samples goal, and all general proof gates OPEN.

## Constructive bridge and falsifiers

- Producer: `InferenceSession::execute_candidate_field_tails` selects a member only after complete receiver, inventory, target, and where evidence; `MemberFreshUse` retains selected member and occurrence.
- Transport: identify the exact active owner and original source owner needed to join one solved use to a runtime code site, including operator-provider FieldTails retained through member FreshUse.
- Consumer: `RuntimeProgram` compiles the authenticated method source and `Machine` applies it to the receiver before any explicit method argument.
- Imported dependency closure: each encountered `SourceExportId` resolves through the exact public export index to its source-owned binding root; local `DefId` references are followed only within the observed HIR world. The compiled imported name is lowered to that exact `DefId`.
- Authenticity: source HIR artifact, `SourceRootId`, occurrence, `SourceMemberRootId`, module identity, and candidate HIR membership must all match. No spelling-only or runtime-shape-only route.
- Falsifiers: absent source carrier; duplicate routes for one code site; two distinct selected members sharing a site without a proved runtime discriminator; explicit method argument lost or reordered; selected member source from a foreign artifact; candidate conflict; incomplete or deferred dispatch.
- Continue to preserve `[io]` in a contravariant position as `[io,'e]`; passing `[state]` is allowed.
- Runtime completion must retain source schedule, lazy value materialization, ordered host writes, and exact output required by R149.

## Exact write leases

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/src/lib.rs`
- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/mod.rs`
- this contract, `notes/theory/2026-10-22-r325-runtime-member-fieldtail.md`, and `tasks/agent-loop/current.json`

All other paths are read-only. Entry SHA-256: `candidate_scheme.rs` `ca259a99cb92fa4d7536c7ea0f1e7043cfed98b4d99addf5477f6b956cf075ed`; `shadow_apply.rs` `dac30ada2586c2949e8bd7c65e481d3dfd2bb51d666ce05c818c80f156be43d0`; playground `lib.rs` `4d8ba6900383d3efc9c1c79a109992789a27b57f838391ab023d5f3518928e08`; runtime `program.rs` `13c927a1b20f89f62bb76ee93ea7d3a95ee6b916bf4b31583ca902eeb5247527`; `machine.rs` `94c7fddf505cfbabb7a36224e1eb5f8095e1595558716e6d186ba6c73a5197ee`; `mod.rs` `4baed82ca7a3eaa89f818cda14a484a24fe5aa7fa5fc1e40f3769e9f9cb2455b`.

## Verification and boundaries

Evidence: unchanged Types executes via CLI with the exact 142-byte source and prints `(42, Yulang)\n`; `unchanged_types_captures_the_exact_host_write_result` and `host_write_response_resumes_its_exact_continuation_once` pass. `cargo test -q -p yu-playground --lib` passes 44 tests, `cargo check -q -p yu-playground` passes, and `git diff --check` passes. `out::write` authorization comes from the exact `std::io::out::write` source operation-path import, its resolved public export identity, and a `str -> ()` signature; dispatch compares `SourceOperationId`, validates a string payload, and returns a unit response through the existing continuation template machinery. These checks are implementation evidence, not a proof of soundness, completeness, principality, source/native adequacy, or theorem closure. Console, R149, source/native obligations, the broader samples goal, and production remain OPEN. Resource cap 2400 seconds, no carryover. Commit and push coherent checkpoints without force-push.
