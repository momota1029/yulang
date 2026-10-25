# Agent orchestration

For the unchanged general contract, read [agent-orchestration.pre-sprint.md](agent-orchestration.pre-sprint.md).
That byte-preserved baseline remains binding outside the precise supersession
scope in [the sprint decision](../notes/design/2026-10-16-goal-driven-sprints.md).

For authorized ongoing `research/simple-sub-intrusion` work,
[goal-driven-sprints.md](goal-driven-sprints.md) is the active scheduling authority.
Its explicit scoped overrides take precedence regardless of read order.

Role permissions, reviewer isolation, proof-coordinator leaf limits, capacity
retry classification, supported fallback and primary-only Git remain binding.
Within the sprint scope, role/model routing and continuation come from the sprint
policy, not the legacy role descriptions or rescue-only Astra examples.

## Lean specialist

Use `lean_prover` for a primary-assigned bounded Lean proof or verification packet.
It inherits configured proof defaults and is always a leaf. Apply
[`yulang-lean-proofs`](../.agents/skills/yulang-lean-proofs/SKILL.md) for source
mapping, pinned execution, diagnostic repair and per-theorem axiom audits.
Ordinary `prover`/`astra_prover` Lean work uses the same skill; unavailable custom
roles use the existing supported generic-worker fallback.

Grant exact proof/handoff paths, frozen inputs, checker/cache ownership, resource
limits and a stop condition. Installation, manifest/root-import edits outside a
lease and source-semantic decisions return to the primary. This role has no
implementation, production, Git, reviewer-appointment or coordinator rights.
The existing proof-coordinator child-role exception is unchanged. Keep independent
meaning/source review separate from actual kernel acceptance.
