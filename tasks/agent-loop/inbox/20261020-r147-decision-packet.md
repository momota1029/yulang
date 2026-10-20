# R147 Luna decision-packet handoff

- Contract: R147 rev2, `tasks/agent-loop/sprints/braced-if-approval-packet-20261020-r147-rev2.md`, SHA-256 `87ec019b57a2e885bff6aab5e7cf16929526ebb07df593646f495442184ff281`.
- Original goal: proof-backed inference/evaluator implementation and broad execution of unchanged Yulang2 Web samples. R70/R71, Simple-sub/evaluator A/B, source/native and production remain OPEN.
- Fixed input: unchanged `web/playground/examples/yulang2-ordinary-islands.yu`; desired selected definition `countdown_result`, expected future output `8\n`. No execution was authorized or performed.
- Baseline: `4d9c9c74e0c56b8e34b60d521b68bcf8504946b2`, tree `e2baa5de4a9796b56fa1a2c85e581346bd54886f`; all 26 direct source pins match. `Cargo.toml`, `Cargo.lock`, `crates/`, `tools/`, `apps/`, and `web/` have no baseline diff.
- Decision draft: `notes/design/2026-10-20-braced-if-compatibility-r147.md`, SHA-256 `2dbbf05c2c74810c4684a71d81933d4b6b4a9be2067dcc60b943bb090ff64f12`.
- Proof note: `notes/theory/2026-10-20-braced-if-elaboration-r147.md`, SHA-256 `f2a9ef20bc981ba40310aaca5ff20f2c0edaff6e60f5e07e63f13fdd33e4094b`.
- Proof-worker handoff: `tasks/agent-loop/inbox/20261020-r147-proof.md`, SHA-256 `02890c687a4be4f82d071cc9c24d4ee728192107e48f0f74dc93fd1b553e1887`.
- Proof author `/root/r147_proof` stopped at `2026-10-20T02:19:53.979209Z`, no descendants. Its elapsed time is unknown; full 420-second proof reservation is charged.
- Prospective spec and compiler/source reviews are CLEAN for exact contract rev2. Luna independently checked all 26 live pins and source-tree parity. Fresh final compiler/source review is pending.

## Source result

The Y2 record predicate runs before the block path. Empty braces and inline fields route to record construction; one operand-bearing spread can carry effect and head/tail record meaning; a second spread fails construction. Non-record groups sequence retained items, while direct ExprSpread is filtered out. This is historical source behavior, not an automatic Y3 rule.

Y3 `if` arms currently require colon bodies. Bare `else { ... }` emits a missing body and hands the brace outward. Current HIR conditional admission accepts colon-form operator/indented blocks only; the existing statement-block builder does not represent arbitrary expression lists. Candidate inference and runtime have an ordered conditional consumer, but that does not prove new source reaches it. The browser UI/smoke do not currently select or execute the ordinary-islands countdown sample.

The singleton argument is conditional on source construction/identity, conservative inference transport, operational simulation with sufficient fuel, and unchanged conditional/module schedule. No proof of those implementation premises, sample execution, Y3 semantic approval, theorem, source/native correspondence or parent closure is claimed. R146 supervisor conformance remains UNVERIFIED.

## User decision after clean final review

- **A: narrow countdown support.** Accept only one ordinary non-record expression and reject other brace shapes explicitly.
- **B: broader expression-list support.** Add a dedicated sequence HIR/inference/runtime path for ordinary expression lists; give empty, record-shaped, and spread cases explicit semantics, preserve record-shaped empty/field/one-spread behavior, reject duplicate spreads and non-record mixed spreads instead of silently omitting an item. This requires a new sequence owner; current Y3 statement-block lowering is insufficient.

Luna recommends B because it supports more unchanged samples while naming the historical mixed-spread omission as a deliberate Y3 rejection. This handoff itself grants no semantic or implementation authority. Only a clean fresh review followed by the user's explicit approval of an exact option can authorize a separate end-to-end implementation contract. No safe code slice exists before that approval.
