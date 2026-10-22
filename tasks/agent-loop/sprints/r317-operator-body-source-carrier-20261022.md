# Sprint R317 — provider operator body source carrier

Status: OPEN; parent Y2 sample outcome and R149 remain OPEN.
Branch / baseline: `research/simple-sub-intrusion` at `acc1d493191dbb032915a8f0b3f314e5a03f31f7`.
Authority: unchanged Yulang2 playground samples; unified design §§4.1–4.5, 5.1, stages 4/10; proof companion §§2.16, 4.1–4.5, 7.1–7.5; R315 exact infix LocalSource; R316 imported operator owner receipt.
Dispatch: serial primary. `next_action_selector` is not callable in the current tool schema. User explicitly prohibits subagents. No independent proof/review is claimed.

## Parent outcome and bounded step

The parent outcome remains that every bundled Yulang2 playground sample passes ordinary tests, with the implementation and source/native proofs complete. R316 now exposes the exact provider declaration/body keys and metadata for a selected imported operator. The source owner still cannot be consumed as an authentic provider source root. Initial inspection showed operator bodies are not ordinary `HirItem::Binding`s; a focused probe then found the RHS is already retained as a direct `HirItem::Expression` with an exact `SourceRootId::Expression` and LocalSource carrier. Candidate collection still has no checked join from `SourceOperatorOwner` to that existing root, so R315's `LocalSourceForm::InfixOperator` remains unavailable.

This sprint authenticates and exposes the existing RHS expression root through a checked `HirModule` lookup that accepts the R316 `SourceOperatorOwner` and the exact selected provider `SourceExportIndex`. The join must match provider module/revision and complete owner receipt, prove the source keys belong to the provider HIR parse, and return one supported expression carrier whose root body range is exact. The source graph must preserve the actual RHS expression and nested operator provenance. Do not synthesize an ordinary binding, choose by spelling, rewrite `+` to `.add`, infer a scheme, type/select/execute the infix use, or change parser semantics.

## Evidence and falsifiers

Outcome evidence: operator RHS appears as an ordinary `HirItem::Expression` (never a value binding), and `HirModule` retains its `SourceRootId::Expression` and LocalSource carrier. The carrier body range equals the exact indexed operator body range; the root source key equals `SourceOperatorOwner.body()`. `LocalSourceForm::InfixOperator` separately preserves the consumer occurrence and parser provenance. The completed checked imported-owner-to-provider-root lookup reuses this carrier.

Falsifiers: the new body root is not owned by the exact provider HIR parse; its body key/range differs from `SourceOperatorOwner`; recovery or private visibility admits a carrier; duplicate provider records select arbitrarily; its local source rewrites or loses any RHS source occurrence/operator provenance; or ordinary definition carriers regress. If no source-root identity can represent the operator declaration without collision or false declaration semantics, stop at the exact invariant and record it.

## Outcome

`HirModule::source_operator_root_for` now joins a public `SourceOperatorOwner` with its exact selected `SourceExportIndex`, verifies module/revision and full receipt equality, checks declaration/body parse ownership, and requires one supported expression carrier with the exact RHS range. The operator RHS already existed as a direct `HirItem::Expression`; no second root or ordinary binding was added. A same-bytes reparse is rejected by the parse brand. The pinned stdlib regression resolves the imported `+` receipt to the existing `core/ops` provider HIR carrier and checks its original `\x -> \y -> x.add y` source slice.

Verification passed: `cargo test -p yu-hir --lib` (166 tests), `cargo test -p yu-playground --lib` (41 tests), `python3 tools/agent_sprint.py check`, and `git diff --check`. This does not admit the consumer infix into candidate collection or type/execute it.

## Proof/implementation work

- Construct the bounded source correspondence directly: owner receipt equality plus provider-parse ownership implies the carrier's root key is the exact declaration body. This proves source identity only; syntax association, body semantics, candidate scheme, soundness, principality and runtime remain separate.
- Implement exact lookup from the owning HIR artifact. Avoid creating a second root or synthetic definition for the operator body.
- Add pinned stdlib coverage that compares imported-use owner, selected provider-index receipt, provider HIR root/body ranges and original body text; retain fail-closed mismatch/recovery/visibility cases from the HIR owner tests.
- Next gate after R317: consume the exact provider carrier as an operator function value and retain the consumer operands/application with correct per-use generalization and effects. Do not claim this sprint implements that gate unless the ordinary candidate path actually does so.

## Leases and resources

Write leases:
- `crates/yu-hir/src/module.rs`
- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-hir/src/module/source_exports.rs`
- `crates/yu-hir/src/lib.rs`
- `tools/inference-playground/src/lib.rs`
- `tasks/agent-loop/current.json`
- this contract and `notes/theory/2026-10-22-r317-operator-body-source-carrier.md`

Read-only inputs: `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/candidate_value_graph.rs`, `crates/yu-solver/src/shadow_apply.rs`, R315/R316 evidence and converted design/proof Markdown.

Baseline hashes:
- `crates/yu-hir/src/module.rs`: `4b8a77ad6d37df82985ae7e0d3a6815b3e39bfecb6243446c8543b106ca32746`
- `crates/yu-hir/src/module/local_source.rs`: `e6280947146eb272692302f571bbfb0601dc7f17aacf7eeec24bfc04b35b7e1a`
- `crates/yu-hir/src/module/source_exports.rs`: `25e3a19e091ea304ee37f3ee8bc24ff77828f4610aaeed65b25a3b58f9c3dd11`
- `crates/yu-hir/src/lib.rs`: `23443e5de71101f1cf62719e32294c9bae9c8a0400be279af3dec8fd5e097470`
- `tools/inference-playground/src/lib.rs`: `ccec7480b2009c7a052fb906c2779a540a8492ce997d1a56630b4fc0fea8bf78`

No subagents or concurrent writers. Solo cap 1800 seconds, zero carryover. Preserve original parser/typing semantics and all expected outputs. Run focused HIR and pinned playground checks, `python3 tools/agent_sprint.py check`, and `git diff --check`. Commit and push one coherent evidence checkpoint while keeping the worktree clean. R149, source/native A/B, principality, termination, independent review and production gates stay OPEN.
