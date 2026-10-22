# Sprint R331 rev3 — fail-closed projection and R149 Web integration

Status: ACTIVE; primary-authorized solo continuation. Supersedes R331 rev2 after the integration audit found unleased renderer/CLI edits and a projection that could print constrained Value rows without showing their constraints. The `next_action_selector` recommended keeping R149 unchanged and proving the projection before Web smoke. No language semantics or parent scope changes.
Branch / baseline: `research/simple-sub-intrusion`, `4efeb7617`.
Authority: R149 `notes/design/2026-10-20-r149-types-console.md`; inference
principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md`;
legacy withdrawal `notes/design/2026-10-10-simple-sub-legacy-withdrawal.md`.

## Original outcome and success evidence

Keep the unchanged Yulang2 samples and the full user goal: ordinary inference,
execution and proof. For R149, Types and Console remain exact source bytes with
their pinned public types and ordered captured writes. Do not add an intrinsic,
rewrite, prefix extraction or injected `main`.

The Simple-sub candidate result currently has no accepted public scheme;
`finish_candidate` asserts absent closed types and schemes. The Types graph shows
`id`'s shared Value row and distinct local argument/result Effect rows with a
retained inclusion between them. `yu_types::ClosedValueScheme` cannot represent
quantified effect rows or operation labels, so it cannot be used as a complete
public type carrier. The current Web path has neither R149 source and exposes
only graph inspection and selected-definition execution.

## Required construction and implementation

1. Define a candidate-owned public scheme that preserves Value and Effect row
   identities, bounds, quantified rows, source operation labels/routes and
   same-use correlations. Derive it from the drained Simple-sub candidate graph
   using its authentic level/boundary and effect-algebra evidence. Do not use
   F5 `shadow_closed_schemes`, collapse effects to empty, or display raw graph
   rows as if they were a principal type.
2. Prove the projection represents the accepted graph observations, preserves
   shared quantified rows and effect residuals, and rejects unsupported,
   ambiguous, conflicting or resource-exhausted states atomically. Apply the
   FieldTail source-to-constraint and runtime identity evidence to the exact
   member application; keep source typing/model premises open until proved.
3. Make the inference playground and WASM return a fail-closed candidate type/effect view and whole-module ordered writes from the same accepted result. Before rendering a type, reject distinct concrete Value lower heads that cannot be represented; retain all Value and Effect bounds, local quantifiers, and external anchors that affect the root. Derive quantification after collecting every row used by the root, permissions, effect operands, and displayed bounds.
4. Update browser examples and UI to run the exact Types/Console sources; Types shows polymorphic `id`, `answer: int`, `name: str`, `pair: (int, str)`, with `(42, Yulang)\n`; Console yields `hello from Yulang\n` then `3\n`.
5. Verify with focused tests, `cargo test -p yu-playground`, and fresh `npm --prefix web/playground run check` when wasm-bindgen CLI is available. Preserve ordinary behavior for related samples and record all uncovered parent proof obligations.

Success is the fresh browser smoke and accepted type/effect projection for both
unchanged samples with a proved source/solver relation. This increment does not
close all Yulang2 samples, full source/native adequacy, complete A/B, principality,
termination, independent review or production admission.

## Exact primary leases

- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_effect.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/src/lib.rs`
- `tools/inference-playground/src/render.rs`
- `tools/inference-playground/src/main.rs`
- `tools/inference-playground/tests/cli.rs`
- `apps/yulang-wasm/src/lib.rs`
- `web/playground/src/main.ts`
- `web/playground/src/wasm/yulang_wasm.js` (generated)
- `web/playground/src/wasm/yulang_wasm.d.ts` (generated)
- `web/playground/src/wasm/yulang_wasm_bg.wasm` (generated)
- `web/playground/index.html`
- `web/playground/src/style.css`
- `web/playground/smoke-test.mjs`
- `notes/theory/2026-10-22-r330-console-role-frontier.md`
- this contract revision
- `tasks/agent-loop/current.json`

Only the primary writes these paths; no reviewer or subagent is active. The
existing frozen source is read-only unless included above. No semantic change,
old-solver bypass, special-case spelling, source restriction or production
promotion is authorized.

## Resources, review and continuation

Primary-only serial work, maximum 900 additional active seconds from the conservative remaining budget; no carryover. At most one heavy
Cargo/build/test process. Review remains UNREVIEWED and solo; preserve frozen
artifacts for fresh independent review when available. The primary stages
explicit paths and pushes non-forced. Continue related proof and implementation
stages under these leases. At a material blocker, counterexample, integration
seam, lease change or sprint end, consult the dispatcher and record its delta. STOP/session end cannot leave an unsupported
RUNNING writer.


## Rev3 delta

The projection audit found two unproven display cases: distinct concrete Value bounds can collapse to a row name while their Value constraints are omitted, and Effect rows appearing only in retained bounds/permission views are not included when the quantifier list is calculated. Until represented completely, these cases must withhold the whole output. The existing generated WASM path is included only as build output; no generated file has been written in this revision so far. Review remains UNREVIEWED and all parent theorem gates remain OPEN.
