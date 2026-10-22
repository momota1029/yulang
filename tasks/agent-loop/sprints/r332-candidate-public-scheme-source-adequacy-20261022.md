# Sprint R332 — candidate public scheme and source adequacy

Status: ACTIVE; primary-only continuation under the user's explicit no-subagent direction. This continues the unchanged parent goal: ordinary Yulang2 playground samples, implementation, proof, frequent commits/pushes, and a clean worktree. It does not narrow the catalog to R149 or treat a candidate view as an accepted principal scheme.

Branch / baseline: `research/simple-sub-intrusion`, `a7013f534`.
Authority: R149 `notes/design/2026-10-20-r149-types-console.md`; inference principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md`; legacy withdrawal `notes/design/2026-10-10-simple-sub-legacy-withdrawal.md`; user correction that negative `[io]` means `[io,'e]` and admits `[state]` while retaining its performed effect.

## Parent goal and this increment

The parent goal remains all unchanged Yulang2 playground samples working through ordinary compiler tests, with implementation and proof completed. Preserve the original sample bytes, outputs, quantifiers, source/native correspondence, and A/B claims. R332 advances the R149 public type/effect path and its source correspondence; finishing this increment does not close the parent goal.

R331 now renders retained effect operands and open tails, fails closed on unsupported type/bound nodes, and collects unresolved Value rows occurring only in displayed bounds into the binder set. Focused Types and `[io]`/`[state]` source tests pass. The full playground suite must be rerun after the bound-only Value quantifier change. `CandidateGraphExport` remains a provisional graph observation, not a candidate-owned accepted scheme; source adequacy and principality remain open.

## Required outcome

1. Build a candidate-owned public scheme value from the drained candidate graph. Preserve one simultaneous Value/Effect row identity map, local quantifiers, external anchors, all bounds, operation labels/routes, formal permissions, open residuals, and same-use correlations. Resource exhaustion, ambiguity, missing source identity, or unsupported nodes must withhold the whole result.
2. Establish the exact graph-to-view correspondence for unchanged Types and the `[io]`/`[state]` regression. Keep formal permission separate from effect contribution and runtime Grant. Negative `[io]` is open `[io,'e]`; `[state]` is admissible and its effect remains in the residual.
3. Apply the evidence to the original source/native and A/B obligations; identify each still-open premise and its owner. Do not invoke F5 `shadow_closed_schemes`, collapse effect tails, introduce sample-specific syntax/intrinsics, or assert principality without proof.
4. Rerun `cargo test -q -p yu-playground`; preserve exact Types/Console outputs and all existing checked browser example behavior. Repair or regenerate WASM bindings and run `npm --prefix web/playground run check` if the pinned CLI becomes available. Keep the missing generated-binding failure explicit otherwise.
5. Keep the broader Yulang2 playground catalog as an active parent requirement. Inventory checked-in examples and tests; add ordinary regression coverage where an existing sample lacks it without changing its semantics.

Success for this increment is a typed candidate-owned public scheme with a checked source-to-graph mapping and full native playground suite, plus a fresh Web smoke when the generator is available. It is not parent-goal completion, full A/B closure, unrestricted principality, production admission, or independent review.

## Exact primary leases

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_effect.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/src/render.rs`
- `tools/inference-playground/src/lib.rs`
- `tools/inference-playground/tests/cli.rs`
- `apps/yulang-wasm/src/lib.rs`
- `web/playground/src/main.ts`
- `web/playground/smoke-test.mjs`
- `web/playground/src/wasm/yulang_wasm.js` (generated)
- `web/playground/src/wasm/yulang_wasm.d.ts` (generated)
- `web/playground/src/wasm/yulang_wasm_bg.wasm` (generated)
- `notes/theory/2026-10-22-r330-console-role-frontier.md`
- this contract
- `tasks/agent-loop/current.json`

Only the primary writes these paths. No subagent, reviewer, or parallel writer is active. Use only one heavy Cargo/build/test process. No language-semantic change or production promotion is authorized.

## Resources and continuation

Primary-only serial envelope: 900 additional active seconds, no carryover; at most one heavy Cargo process. Review stays UNREVIEWED; no self-review claim. Commit coherent verified checkpoints, push non-forced when network allows, and preserve a clean worktree after each checkpoint. At the sprint boundary, keep the parent goal active and record the exact remaining source/proof/tooling premises.

## Direct-primary continuation, 2026-10-22

The current user explicitly selects direct primary proof/code work with minimal
sprint records and no routine subagent dispatch. This overrides the historical
Luna-primary and Astra-child routing for this continuation, without changing
semantic authority or independent-review requirements. No child is launched.
The fresh runtime listing contains only `/root`; the three legacy UNKNOWN
identities remain quarantined and are not reclaimed.

Continue the same outcome with a typed finite graph projection (including
constraints and exact effect provenance) and a constructive correspondence
argument. Add the exact primary lease `tools/inference-playground/src/scheme.rs`
for this representation; existing renderer/lib/test/receipt leases remain.
Use a 3600-second direct-primary envelope from this resumption, retaining the
previous 300-second charge separately. One heavy build/test process at a time.
The current primary's effective model/effort is not asserted from the user's
model label. Research checkpoints remain explicitly UNREVIEWED.

The same continuation also leases
`tools/inference-playground/tests/runtime_resume.rs` for the observed unused
`mut` warning only. It is a separate mechanical checkpoint; assertions and
expected outputs are unchanged. The public types/module-events join remains
inside R149's existing same-inference-result publication requirement.

The direct continuation additionally leases `crates/yu-solver/src/candidate_source.rs`.
The transitive library dependency counterexample requires exact provider closure
and operator constraints at their source positions before enclosing capture.
Extend the source dependency schedule across existing definition SCCs and
operator provider roots; preserve authentic receipts, same-FreshUse maps,
and unavailable results for unsupported cyclic provider dependencies.
This is a construction-order repair under existing inference authority.
The same slice leases `tools/inference-playground/src/runtime/program.rs` for
the exact source-owner evidence join after enclosing capture ownership changes;
no runtime shape dispatch or member-choice fallback is authorized.
