# Sprint R318 — operator provider HIR projection

Status: RESULT / OPEN_CONTINUATION; parent Y2 samples and R149 remain OPEN.
Branch / baseline: `research/simple-sub-intrusion` at `2086ccf25f3a787e0c2775075c711ae5f6e485ce`.
Authority: unchanged Yulang2 playground samples; unified design §§2.2–2.3, 4.1–4.5, 5.1, stages 4/10; proof companion §§2.16, 3–4, 7–8; R316 authenticated operator owner; R317 provider expression-root join.
Dispatch: serial primary. `next_action_selector` is unavailable in the current tool schema; user explicitly prohibits subagents. No independent review is claimed.

## Parent outcome and bounded step

The unchanged Yulang2 samples must pass ordinary tests, with implementation and source/native proof complete. R317 resolves an imported operator receipt to its exact existing provider HIR expression root. However, `pinned_provider_projection` currently traverses only imported value `Name` exports, so the operator provider HIR is absent from the candidate module world unless another value import happens to pull it in.

Extend pinned provider projection to traverse exact imported `LocalSourceForm::InfixOperator` occurrences, resolve each through the consumer's `SourceImportEnvironment::operator_owner_for_use`, and include the exact provider RHS root under its selected source index. Accumulate operator body roots and ordinary selected value roots in the same per-module selected-root set without reconstructing the parse or losing its parse brand. Fail closed on a missing/ambiguous owner, mismatched dependency/index, foreign parse, or duplicate projection.

This is module-world/source-root projection only. It does not turn the provider expression into a generalized operator value, link consumer operands, admit the infix in candidate collection, type the expression, choose a method, run the sample, or close R149.

## Correspondence and falsifiers

Source premises: the consumer LocalSource contains the exact operator `HirOperator` provenance; R316's owner is authenticated by selected syntax dependency path/revision and provider declaration range; R317 joins that owner to a unique provider expression root whose source key/range match the provider parse. Projection must retain that provider HIR in the same pinned source world consumed by candidate solving.

Falsifiers: provider HIR absent from the candidate module list; wrong source index chosen; provider HIR rebuilt from different bytes/parse identity; consumer route guessed by spelling; same provider roots duplicated or ordinary imported roots lost; or the projection changes parser, type, or runtime semantics.

## Work and exact leases

- Implement operator-owner discovery and provider-root projection in `tools/inference-playground/src/lib.rs`.
- Extend pinned provider projection regression to show the exact `core/ops` provider root is present when selected by an imported operator use; retain the existing independent regression for ordinary imported value roots.
- Keep a proof receipt identifying each premise and its source owner; this is a bounded source correspondence result only.
- Read-only dependencies: HIR `source_operator_root_for`, `SourceImportEnvironment`, `SourceExportIndex`, candidate collection entrypoints, R316/R317 receipts, and converted design/proof Markdown.

Write leases: `tools/inference-playground/src/lib.rs`, `tasks/agent-loop/current.json`, this contract, and `notes/theory/2026-10-22-r318-operator-provider-module-projection.md`.
Baseline hash for `tools/inference-playground/src/lib.rs`: `6efc2c1db7c4f719155e6517cd5935dd22cb00d6e3106c0be4c4a5daae551f09`.

Solo cap 1800 seconds, zero carryover. Focused operator projection test passed; `cargo test -p yu-playground --lib` passed 42/42; `python3 tools/agent_sprint.py check` and `git diff --check` passed. The operator and existing ordinary-value projection regressions are separate because the pinned operator provider exposes operator declarations rather than ordinary bindings. Commit/push a coherent source-correspondence checkpoint. Existing warnings in direct dependencies `yu-hir` and `yu-solver` were observed; their owning paths are outside this lease and remain a separate audit item. R149, source/native A/B, principality, termination, independent review, candidate typing, runtime and production remain OPEN.
