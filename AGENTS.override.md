# Simple-sub sprint entry point

Read root [AGENTS.md](AGENTS.md) explicitly; this override must not hide the
repository's hard invariants or conversation/artifact conventions.
For authorized ongoing work on `research/simple-sub-intrusion`, apply
[rules/goal-driven-sprints.md](rules/goal-driven-sprints.md) and
[the sprint skill](.agents/skills/yulang-sprint/SKILL.md).
The [2026-10-16 sprint decision](notes/design/2026-10-16-goal-driven-sprints.md)
replaces the former resident-loop cadence and rescue-only Astra restrictions.

Luna owns authority, actual dispatch, exact leases, review and Git. The existing
`next_action_selector` is the lightweight sprint dispatcher. Keep the Luna/high
implementation lane and a constructive proof lane; Astra can own a bounded
multi-stage core proof while Sol independently investigates complementary questions.
Consult the dispatcher at sprint start/end, material blockers/counterexamples,
authority/dependency/lease changes, integration seams or goal replanning, not
at every completed lemma, test, result, review receipt or internal next step.

Use the compact current state, never a historical RUNNING row, to prepare live
reconciliation. Unknown writers retain quarantined leases. STOP/session end
cannot leave a worker recorded RUNNING without current runtime evidence.
Maintenance alone starts no workers, changes no compiler semantics, and does
not authorize a background service. Children never start their own sprint team.
