# Proof and task-decomposition role delivery

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Inspected remote baseline: `6bb5c314af7cb62da762a0198417629fb4273e17`
Status: configuration/policy verified and independently reviewed; live runtime adoption unobserved

## Scope and authority

The user explicitly requested GPT-6.1 Sol proof and task-decomposition roles,
with bounded proof parallelism and escalation to Astra. The
[workflow decision](../design/2026-10-10-proof-and-task-decomposition-roles.md)
records that authority. This is an M2 bounded orchestration-contract change:
one independent conformance reviewer covers role/model routing, descendant
budgets, lease lifecycle and review isolation. No compiler, semantic, theorem-
status, production adoption or expected-output changes are in scope.

The isolated review checkout's policy/configuration blobs match the inspected
remote baseline. The two shared metadata files were refreshed exactly to that
baseline before adding only workflow navigation. Other worktrees and their
uncommitted research artifacts were not modified.

## Changed responsibilities

- New `prover`: normal Sol/high via existing defaults; no role model/effort
  pins, preserving a real native Astra override path. Proof coordination needs
  a primary-issued packet and has at most two leaf workers with no redelegation.
- New `task_decomposer`: pinned Sol/medium, read-only, concrete packets and
  critical path; neither scheduling nor recurring plan churn.
- Existing `researcher`: complementary falsification/experiment/source work.
- Root routing, research budgets, assignment seed and Git lease rules use the
  same narrow delegation exception. Existing primary/specialist model pins,
  global thread ceiling, independent-review and primary-integration duties remain.

## Validation record

The primary's focused Python validation passed: all 12 TOML files parse, all
11 role identities and required fields are valid, existing model/effort/sandbox
pins and primary configuration values are preserved, the proof default and
unpinned Astra override route are consistent, and decomposition is Sol/medium
with a read-only sandbox. Eight added local links/anchors resolve. The exact
14-path scope matches the intended change; `git diff --check` passes. All
pre-change blobs match the inspected remote baseline, including the exact
refreshed task/index files.

Fresh independent GPT-6.1 Sol reviewer `role_policy_review` reported no
BLOCKING, major or minor findings across model resolution, role format,
one-generation delegation, aggregate budgets, interruption/lease lifecycle,
primary authority, independent review, fallback and concrete proof work. The
reviewer separately parsed the 12 TOML files. Subsequent changes only filled
review/status records; no functional repair was required.

Zero Cargo builds, benchmark processes or broad compiler tests ran: compiler
behavior is unchanged. Static checks do not establish local Codex role discovery, live model routing,
nested runtime capacity, or hot reload; those remain unobserved in this task.

Before publication, recheck the remote head and changed-path baselines, retain
unrelated concurrent commits, and update only the intended branch by an
expected-head fast-forward. Record the actual publication outcome in the final
report; no hypothetical worker or runtime launch is a completed action.
