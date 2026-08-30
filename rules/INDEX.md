# Yulang repository rules

`rules/` contains active, durable repository policy. Root `AGENTS.md` is only the operating map and user-facing communication contract; it must point here instead of copying these rules.

## Authority and orchestration

- [`design-authority.md`](design-authority.md) — authority order, design status, approval, supersession, and legacy provenance.
- [`orchestration-budget.md`](orchestration-budget.md) — lightweight operating modes, reviewer/round limits, delta review, measurement/verification budgets, and progress-record ownership. It is authoritative over broader reviewer-count wording elsewhere.
- [`agent-orchestration.md`](agent-orchestration.md) — specialist roles, task routing, information isolation, review loops, and handoffs.
- [`legacy-compatibility.md`](legacy-compatibility.md) — interpretation of historical Claude/Codex/Fable/Level terminology without reviving retired policy.
- [`workflow.md`](workflow.md) — task context, handoffs, scoped execution, progress records, decision points, and completion reports.
- [`git-concurrency.md`](git-concurrency.md) — worktree isolation, staging, commits, branch safety, and integration ownership.

## Compiler engineering

- [`compiler-engineering.md`](compiler-engineering.md) — responsibility boundaries, file/module shape, diagnostics, experimental mechanisms, and comments.
- [`parser-chasa.md`](parser-chasa.md) — repository-specific `chasa` parser-combinator conventions.
- [`bug-fixing.md`](bug-fixing.md) — root-cause diagnosis, repair placement, temporary workarounds, and scope discipline.
- [`performance.md`](performance.md) — hot paths, recomputation/allocation policy, adaptive measurement budgets, and resource-risk triggers.
- [`testing.md`](testing.md) — focused verification, broad-check budgets, regression structure, expected-output protection, and heavy-suite safety.

## Prose and model operation

- [`documentation.md`](documentation.md) — public documentation and style-guide routing.
- [`codex-quirks.md`](codex-quirks.md) — observed agent failure patterns and verification countermeasures.

Design-document navigation lives in [`notes/design/INDEX.md`](../notes/design/INDEX.md). Historical incidents live under [`notes/incidents/`](../notes/incidents/); incident records are not automatically active command policy.
