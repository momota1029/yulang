# 2026-07-08 shadow (weighted-routing replay) necessity investigation

Read-only investigation via Codex MCP (gpt-5.6-sol, xhigh), delegated by Claude, following up on the 2026-07-06 infer/constraint-solving bottleneck investigation's proposed next step ("measure whether shadow's downstream consumers actually need it"). Note: that exact phrasing was not found verbatim in existing notes/design or notes/todo entries during this investigation -- it originates from Claude's own session memory of the 2026-07-06 investigation, not a written repo artifact.

## Premise correction (read this first)

The premise that motivated this investigation -- that `shadow` (the weighted-var-var-routing replay/observability structure) is the cost driver behind the default-path `lower.resolve` bottleneck -- does not hold. `shadow` (`ConstraintMachine`'s `replay_routing_shadow: Option<RefCell<ReplayRoutingShadow>>`) is constructed only when specific opt-in environment flags are set; in an ordinary default run with no such flags, it is never instantiated at all. There is therefore no basis for attributing the default `lower.resolve` cost (1.285s in the 2026-06-23 hardening baseline) to `shadow` construction or maintenance. **What actually consumes that time in the default path remains unidentified and is a separate, still-open question.**

## What `shadow` is and where it's needed

`shadow` originates in `ConstraintMachine::new()` (crates/infer/src/constraints/mod.rs). Once an accepted canonical constraint `Pos::Var(source) <: Neg::Var(target)` first enters `seen`, it's recorded as an edge. It carries: an all-edge weighted graph, a frontier graph with redundant edges pruned, an exact positive-path cache, interned `ConstraintWeights`, an opt-in all-pairs summary, and measurement counters. It accumulates across `lower.bodies`, `lower.resolve`, and `lower.drain` -- not scoped to `lower.resolve` alone.

Necessity by path:

| Path | Is `shadow` needed? |
|---|---|
| Default compiler path (no env flags) | No -- never constructed |
| Opt-in measurement/metrics path | Yes, for the metrics themselves -- not for correctness |
| Opt-in evidence-only prototype (`YULANG_REPLAY_EVIDENCE_ONLY_SKIP=1`) | Yes, specifically the weighted frontier piece -- removing it without the frontier graph reproduces a previously-broken state: lost public latent effect / disappearing residual row (nested handler, `parse.choice`), matching the earlier failed "direct skip" attempt |

Downstream consumer detail (all four call sites, three run modes):

- `observe_routing_shadow()` -> `observe_edge()` -- records accepted var-var edges. Unneeded by default; needed for weighted metrics and the evidence-only prototype.
- `observe_weighted_routing_consequence_shadow()` -- consequence-coverage metrics; observation-only, short-circuits internally under evidence-only-only mode.
- `should_store_replay_as_evidence_only()` -> `has_frontier_path()` -- decides normal vs. evidence-only bucket; load-bearing under the evidence-only prototype, always false by default.
- `ConstraintMachine::timing()` (-> CLI formatter) -- reports graph/search/cache metrics; not needed for correctness, only for measurement output.

When the frontier check is true, the resulting evidence-only bounds feed two further load-bearing consumers: `compact`/`generalize`'s `projection_lowers()`/`projection_uppers()` (public latent effect + co-occurrence -- this is exactly where the earlier direct-skip attempt broke `compose`/`apply`), and the future-replay scan triggered when a new normal bound arrives (nested-handler / `parse.choice` residual rows). Ordinary selection probing (`.lowers()`/`.uppers()`) does not read evidence-only bounds and does not need `shadow`.

## Bottom line

- No case for reviving the "direct skip" approach -- it's confirmed unsafe for the evidence-only prototype specifically.
- No case for treating `shadow`/weighted-routing-replay as the cause of the default `lower.resolve` cost -- it isn't present in that path.
- Genuinely open decision (not resolved here): whether to keep maintaining the evidence-only prototype, or retire it as a completed past experiment. If retired, `shadow` could likely be dropped from the semantic path entirely (metrics-only consumers could be gated separately); if kept, its two load-bearing consumers above must stay intact.
- **Still unanswered, and the actual next step if the default-path `lower.resolve` cost is to be addressed**: profile/attribute what specifically is expensive in the default path (no shadow flags set) inside `lower.resolve`, since this investigation rules out `shadow` as the explanation.

Investigation: Codex MCP (gpt-5.6-sol, xhigh), read-only, 2026-07-08. Files inspected: notes/design/2026-06-24-weighted-var-var-routing.md, notes/todo/performance-localization.md, notes/todo/static-analysis-speed.md, notes/benchmarks/2026-06-23-hardening-baseline.md, docs/infer-solver-invariants.md, crates/infer/src/constraints/mod.rs, crates/infer/src/constraints/machine/{entry,bounds}.rs, crates/infer/src/constraints/timing.rs, crates/infer/src/lowering/body/mod.rs, crates/infer/src/analysis/session/lifecycle.rs, crates/infer/src/generalize/mod.rs, crates/infer/src/compact/collect/{mod,type_nodes}.rs, crates/yulang/src/source/format.rs, scripts/evidence-only-replay-smoke.sh, scripts/hardening-smoke.sh, crates/infer/src/lowering/tests/case_05.rs. No source code changed; no commits from the investigation itself.
