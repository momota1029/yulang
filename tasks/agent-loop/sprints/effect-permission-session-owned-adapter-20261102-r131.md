# R131 — session-owned permission adapter

Status: ADMITTED. Parent objective remains the original source-preservation/soundness and effect-hygiene goal; this packet repairs one provisional source-evidence adapter only.

## Parent obligation and accepted meaning

Preserve the original Simple-sub A/B claims for every supported original program, source constructors, quantifiers, and the selected annotation policy in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2. Contravariant concrete annotations grant function-local subtraction permission; covariant concrete annotations allow concrete effects; symbolic variables retain their constraints. The actual handler performs subtraction. No policy, source domain, inference behavior, or expected result changes here.

The implementation parent remains the missing source-owned admission/transport from actual App/Lambda construction through propagation and the actual Catch/provider consumer. R112/R114 and the Rust-to-Lean correspondence remain OPEN. The adapter is unused and read-only; even a correct certificate is not an effect constraint, consumer, handler selection, subtraction, or production behavior.

## Exact scope and frozen input

Target is only the implementation candidate for `candidate_scheme::bind_native_formal_entry_permission_use` at current line 505. This packet does not edit Rust source. The author owns only `tasks/agent-loop/inbox/effect-permission-session-owned-adapter-r131-source.md`. The complete candidate must be reconstructed in memory from these authenticated inputs and the preexisting adapter/call-site inventory:

- `crates/yu-solver/src/candidate_scheme.rs` — 4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470
- `crates/yu-solver/src/candidate_effect.rs` — 4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15
- `crates/yu-solver/src/lib.rs` — 429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be
- `crates/yu-solver/src/candidate_call.rs` — fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f
- `crates/yu-solver/src/candidate_intrusion.rs` — 475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97
- `crates/yu-solver/src/term.rs` — d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1

Baseline branch HEAD at admission is `4e4ea3c82c6a117bf82624fcdbcb1f5afe05490f`; `candidate_scheme.rs`, `candidate_effect.rs`, and `lib.rs` are dirty, pinned by their complete hashes above. Do not read or edit quarantined `tools/inference-playground/src/runtime/machine.rs` or `receiving.rs`. Do not stage or change any source file or Git index.

## Required candidate construction

Replace the independently supplied `route`, `BranchTermArena`, `candidate_effect::State`, formal-registration slice, registration number, and occurrence with an entry point that takes `&InferenceSession`, a route index selected within that session's `candidate_graph.routes`, and an incidence index within that route. Derive all evidence inputs from that single borrowed session: route from `session.candidate_graph`, term arena from `session.store.terms`, effect state from that graph's `intrusion.effect_algebra`, and formal inputs from `session.batch.candidate_calls.formals`. Derive registration and Lambda occurrence from the selected retained incidence, not parallel caller values. Preserve the current positive Function/child-1/graph-row/FreshUse/native-field checks and `State::bind_formal_entry_permission_use` source checks. Keep the returned permission borrowed from those session-owned fields for the same lifetime.

This is a direction to construct and review an exact patch candidate, not authority to add a public session brand, mutate inference, change solver decisions, add Catch consumption, or infer a missing source/Lean law. If visibility, feature gating, owner types, route indexing, or Rust privacy make this exact shape invalid, report the exact obstruction instead of adding a freely constructible wrapper or weakening the ownership test.

## Evidence and independent review

Author handoff must include the exact unified patch against pinned `candidate_scheme.rs`, old/new SHA-256 and byte counts, unique hunk anchors, and an ownership table mapping every adapter input to an actual `InferenceSession` field and selected route/incidence. Reconstruct the patch independently in memory and verify its target hash. No compiler, Cargo, tests, formatter, build, environment/storage probe, scratch file, or source materialization is allowed in R131. Compilation remains governed by R111; Cargo allowance is 0/1.

A fresh `compiler_referee` reviews the frozen handoff and source pins. It must attack two sessions over the same HIR with colliding numeric route/formal indexes and attempt to inject B's state/registrations into A's route. PASS requires the API to make such mixed references unrepresentable through its arguments, while retaining all existing admission conditions. A wrapper that accepts externally assembled mixed owners fails. Reviewer writes no files and runs no compiler.

## Resource and stop boundary

Implementer allowance 600 seconds, reviewer 240 seconds, primary integration/state/outcome 360 seconds; aggregate ceiling 1,200 seconds. Additional check/build/test invocations 0; Astra 0. If the exact owner path cannot be established from the pinned fields, a behavior change is needed, any dependency hash changes, or review finds a session mix path, freeze the first obstruction and stop.

Success is an independently reviewed, exact in-memory source candidate that binds every certificate component to one session. It does not establish compilation, execution, Rust-to-Lean correspondence, R112/R114 transport, effect hygiene, original A/B closure, or production readiness. R111's uncompiled-source push decision remains separately pending with the user; R131 grants no source-push permission.
