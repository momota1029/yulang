# Sprint EFFECT-PERMISSION-NATIVE-SNAPSHOT-OWNER/20261031-R34 — bind callback coordinates to the retained HIR owner

Status: CANDIDATE pending exact dependency checks and Luna admission.  
Branch/baseline: `yulang3` at inspected worktree `HEAD afd05a2aaec63890629d97a663a7aff54574075b`; existing checkout only.  
Authority: user's ongoing Rust/Lean effect-hygiene and soundness goal; `AGENTS.md`; `rules/goal-driven-sprints.md`; R33 outcome.  
Contract revision 1. Luna primary approval is the admission receipt created after dependency checks.

## Original outcome and success evidence

**Original parent:** candidate native effect-permission callback translation in R33/R32, followed by the unchanged whole-language Simple-sub A/B, effect-hygiene, inference/executor soundness, principality, progress, termination and production obligations. This sprint closes only the source owner for snapshot identity; it does not close those parents.

**Accepted semantics:** callback coordinates identify data from one immutable HIR snapshot. A cloned `Arc<HirModule>` remains the same snapshot. A separately allocated `HirModule` is a different snapshot even if structurally equal. A foreign snapshot's coordinates must not decode under the retained owner. No equality by source spelling, Debug, serialized index, or structural content is accepted.

**Implementation outcome:** add a private opaque `HirSnapshotToken` in `tools/inference-playground/src/runtime/program.rs`, backed by a clone of the exact `Arc<HirModule>` already retained by `RuntimeProgram`. Compare tokens with `Arc::ptr_eq`, and expose only an owner-issued clone/accessor needed by future coordinate binding. The strong Arc token keeps the source owner alive and cannot be reused while retained. Each `RuntimeProgram` constructor stores the same `hir` Arc it receives. This allocates no new work environment and adds no counter, global state, dependency, cache or heap-sized snapshot copy.

**Proof outcome:** construct a Lean ownership/coordinate model whose token denotes one retained immutable snapshot. Prove cloned owner tokens remain equal, distinct owners reject foreign coordinates, bounded family/operation decode returns exact structural identities, full row preservation holds, and successful translation supplies R32's actual coverage and round-trip premises. Report source-to-Lean correspondence explicitly; the Lean model does not execute Rust or prove allocator internals.

**Source limitation:** `tools/inference-playground/src/runtime/machine.rs` and `receiving.rs` remain quarantined. Do not read or modify them. Freeze a source-qualified integration patch proposal showing how those serializers bind the owner-issued token and check it before coordinate use. Do not claim serializer integration, compilation, runtime behavior, or production readiness.

**Success predicates:**

1. Frozen Rust source change mints no token from coordinates; the only token source is the retained `Arc<HirModule>` owner, clones preserve identity, and separately allocated HIR owners compare unequal.
2. The Lean translation composes owner binding with R33's checked coordinate/complete-row translation and derives R32 coverage/round trips rather than assuming them.
3. A fresh reviewer validates owner construction, clones, foreign-owner rejection, full row, theorem types/full axioms, integration proposal and limitations.
4. No environment/worktree/project copy, Cargo/Lake build, test, target/cache, extraction, scratch directory, or quarantined source access occurs. Only exact leased files are written.

## Two continuing lanes

**Rust implementation — `/root/effect_permission_r31_rust` (Luna/high requested; observed settings UNKNOWN unless runtime reports them):** inspect and edit only `tools/inference-playground/src/runtime/program.rs`; add the owner token and accessor there. Produce `tasks/agent-loop/artifacts/native-snapshot-owner-r34.patch` for the quarantined serializer integration as a clearly labeled proposal, plus one handoff `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-rust.md`. No compiler/build/tests/runtime in this storage-constrained packet.

**Constructive proof — `/root/effect_permission_r31_lean`:** write only `notes/theory/lean/YulangClosure/NativeSnapshotOwnerR34.lean` and `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-proof.md`. Preserve the exact R33/R32 prefix. Use pinned Lean 4.35.0 on stdin under read-only bwrap, report every theorem type and complete axiom list, and apply the owner law to the R33/R32 translation. No hidden assumption may assert the target round trip or same-snapshot uniqueness.

**Independent reviewer — `/root/effect_permission_r31_review`:** after both producer outputs freeze, review only `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-review.md`. Reviewer must inspect the exact source diff and frozen handoffs, check source owner and constructor coverage, challenge the Arc identity premise, audit all declarations and full axioms, and preserve the boundary that serializers are not integrated.

Astra: 0. No Sol coauthor/reviewer substitution. Luna owns exact leases, state, adjudication and Git.

## Permissions and resources

Exact write leases:

- Rust: `tools/inference-playground/src/runtime/program.rs`; `tasks/agent-loop/artifacts/native-snapshot-owner-r34.patch`; `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-rust.md`.
- Lean: `notes/theory/lean/YulangClosure/NativeSnapshotOwnerR34.lean`; `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-proof.md`.
- Reviewer after producer freeze: `tasks/agent-loop/inbox/effect-permission-native-snapshot-owner-r34-review.md`.
- Luna: this contract, its input manifest/admission, R34 stage ledger, `tasks/agent-loop/current.json`, and R33/R34 outcomes.

Exact read dependencies: R33 contract/outcome/manifest, Rust proposal/handoff, Lean module/proof, independent review; `tools/inference-playground/src/runtime/program.rs` baseline SHA `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`; `crates/yu-hir/src/module.rs` SHA `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`; R30 archive/member hashes pinned by R33. Quarantined runtime paths are excluded even from reads.

Fresh envelope 6,000 seconds: Rust 1,600; Lean 1,600; review 1,200; Luna 1,600 including 500 closeout; Astra 0. Transfer no R33 time. Record actual or UNKNOWN runtime and elapsed facts.

Stop if the exact Arc owner cannot be used without accessing quarantined consumers; if any distinct owner can compare equal; if the token must outlive the retained HIR but does not keep it alive; if proof closure requires assuming the target; or if storage expands. Return to Luna before any path, semantic, dependency or resource change.

## Frozen seam and parent application

Review accepts only the exact source and proof revisions. `Arc::ptr_eq` is the proposed identity relation for a retained Arc allocation; structural equality of HIRs is intentionally insufficient. Source-to-Lean map must state this relation and its lifetime domain. R34 does not establish annotation provenance, request emission, Grant/observation authenticity, invocation scope, native Step/History, arm-body result, whole-language hygiene/soundness, original A/B, principality, progress, termination, or production.

At closeout, consult `next_action_selector`, freeze a unique outcome, update compact current state, and run `python3 tools/agent_sprint.py check`. Only Luna stages explicitly intended paths and attempts a safe commit/push; preserve all unrelated changes and deletions, never force-push. No commit or push may include unreviewed or unrelated paths.
