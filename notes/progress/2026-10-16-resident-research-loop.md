# Resident research-loop workflow update

Date: 2026-10-16
Scope: user-requested subagent/skill orchestration only
Initial inspected baseline: `5089bffe706b02bffd2edc80ec8cddb25b47d416`
Integration baseline: `f109376da42e76ee61bb5ec924f78e94da7f44af`
Decision: [resident loop](../design/2026-10-16-resident-research-loop.md)

## Changed behavior

Keep the Luna primary and three resident logical roles: the existing
`next_action_selector` becomes the dispatcher, alongside `implementer` and
`prover`. Luna consults at every next-action boundary, not only when stuck.
Each producer submits mutual TODOs in an exact separately leased inbox file;
the dispatcher alone maintains the scheduling board and selects ready work.
The implementation lane receives an authorized successor whenever one is ready,
without waiting for unrelated proofs. Genuine A/B prerequisites remain intact.

The three roles inherit Sol/high and permit supported bounded Astra overrides.
The normal global thread ceiling remains 12. Actual sandbox permissions belong
to the parent, not role-local sandbox fields; path leases remain coordination
contracts. Children do not recursively start their own trio. A resident lane can
wait between bounded assignments; no daemon or closed-session execution is implied.

The root `AGENTS.override.md` explicitly reads the original operating map, then
applies the narrow superseding decision. Existing historical designs, unrelated
specialists, compiler files, test expectations and pending questions are unchanged.
`tasks/agent-loop/board.md` starts honestly NOT-STARTED and is the dedicated
current workflow record. Existing `tasks/current.md` and `tasks/research-lab.md`
are intentionally not rewritten: this maintenance task changes no research gate
or actual worker status, and another session owns the live research handoff.
The first runtime consultation reconciles those records and actual leases.

## Verification

Local Python static validation: 9 checks passed (unittest; tomllib and YAML).
Checked Luna and global budgets, all 12 role registration paths against the
inspected repository tree, the three unpinned Sol/Astra routing configurations,
both skills' frontmatter/UI metadata/implicit invocation, relative links,
branch-scoped instruction discovery, mutual TODO/single-writer/implementation
refill clauses, truthful initial runtime state, clean whitespace and conflict
markers. Static precedence checks do not execute either model.

No compiler builds/tests/benchmarks were run: no compiler code changed. No live
Codex/subagent tools or independent reviewer were available in this maintenance
environment. Live registration, actual model routing, long-running liveness and
independent workflow review remain unverified; no worker launch or proof closure
is claimed. Follow the decision's bounded live smoke check in the user's runtime.

The remote advanced by four disjoint research commits during editing. Their
changed paths do not overlap this workflow patch, so they are preserved as the
integration parent. Publish the coherent workflow patch using a non-forced
expected-head ref update; recheck and reconcile rather than overwrite if it moves.
