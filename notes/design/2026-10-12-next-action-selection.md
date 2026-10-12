# Evidence-based next-action selection

Status: Authoritative
Scope: additive Codex next-action role and repository skill
Requested-by: user's explicit 2026-10-12 request to add a subagent and skill helping the Luna primary identify the next work
Approved-by: that explicit additive workflow request; no broader automation or semantic change
Approved-at: 2026-10-12
Drafted-by: primary with bounded read-only architect input
Reviewed-by: independent spec_auditor next_action_review; proof-first major finding repaired, design delta PASS
Supersedes: none

## Intended decision

Add a read-only `next_action_selector` and the repository-scoped
`yulang-next-action` skill. Keep the selected primary and existing specialist
settings. The selector chooses the next evidence-producing action when the
primary cannot identify an executable next step; `task_decomposer` expands a
selected direction into dependency-aware packets when needed. Neither role
schedules workers, allocates leases, decides semantics or closes proof gates.

Inspect a pinned baseline, accepted authority, current records and relevant
owning constructors/consumers. Read large progress records by heading and bounded
sections rather than dumping the full history. Distinguish current claims from
historical, superseded, conditional and reviewed results. Report uncertainties
and inspect conflicting evidence before selecting an action.

The result selects one priority action, identifies the first missing premise
and its owner, explains its downstream value and supplies an executable packet:
exact inputs and proposed output paths, role/method, discriminating evidence,
verification owner, resource bound, acceptance criterion and stop condition.
Up to two independent ready actions may accompany it if genuinely useful.
Blocked actions identify their missing evidence or decision and prerequisites;
an absent construction does not by itself prove source rejection.

For a repeated conditional proof attempt at the same premise, identify the
previous attempts and the new method, input or owner that can change the
outcome. If none exists, recommend the owning construction or existing design
decision path rather than an equivalent attempt. Preserve original theorem
scope and required A/B gates; do not invent stronger prerequisites or weaken
approved source behavior. Keep independent authorized work available.

When an open A/B invariant can invalidate a proposed inference mechanism,
prioritize its original-scope constructive proof and independent falsification
or source correspondence before broad dependent implementation. Name the
decisive invariant, actual constructor/consumer owner and proof status. Mark
dependent implementation blocked, or narrowly provisional only for essential
reversible source evidence. Independently justified ready work can proceed.

## Invocation and integration

Use the selector on an unclear next step, restart with conflicting records, or
repeated unchanged obstruction. Already executable packets proceed directly;
the selector does not run after every result. The primary validates authority,
baseline/dependencies and leases, then dispatches the selected ready action
under the existing task authorization. A request only to plan stays read-only.

Pin the role to `gpt-6.1-sol` / `medium`, read-only, using the existing role-file
and registration format. Put the skill under `.agents/skills` for repository
discovery, with implicit invocation enabled. A missing custom role uses one
supported read-only equivalent assignment carrying the role instructions; if
spawning is unavailable, the primary uses the same selection contract directly.
No nested CLI, runtime-limit bypass, model escalation or claimed hot reload.

## Scope and evidence

This changes configuration and workflow only. No compiler code, language
semantics, theorem status, tests, runtime probes or performance measurements
are authorized by this task. Treat this as M2 workflow/configuration work. One
independent `spec_auditor` reviewed the design
and frozen implementation with no remaining findings. Python `tomllib` parsed
both role configuration files and verified registration/settings; the skill
creator validator and metadata YAML parse passed; `git diff --check` passed. No
compiler tests, builds or measurements ran. Record requested versus observed
runtime role/model provenance.

Configuration checks establish file validity, not live registration or improved
Luna behavior. A bounded read-only exercise may provide example behavior; it
does not certify proof closure or long-running planning quality. Existing
concurrency, review budgets, question-board ownership and Git duties apply.

References: [role registration](https://developers.openai.com/ja-JP/docs/config-file/config-reference),
[repository skills](https://learn.chatgpt.com/docs/build-skills),
[orchestration](../../rules/agent-orchestration.md), and
[budgets](../../rules/orchestration-budget.md).
