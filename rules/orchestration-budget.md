# Orchestration budget and operating modes

This file controls default reviewer activation, reviewer count, repair rounds,
delta-review scope, verification/measurement budgets, and progress-record
ownership. Role responsibilities remain in `rules/agent-orchestration.md`.

When an older routing table says several reviewers are mandatory, read it as a
list of eligible risk specialists subject to this budget. A user-approved
Authoritative design still controls behavior; this file controls how much
process is needed to implement and verify it.

## Default principle

Use the lightest mode that covers the concrete changed risks. The existence of
an agent role is not a reason to invoke it. Uncertainty must be tied to a named
semantic, conformance, regression, performance, or public-surface risk before
it raises the mode.

## Operating modes

### M0 — mechanical / records

Examples:

- formatting, typo, link, index, metadata, commit locator;
- progress/status updates;
- a fully specified move or rename with no behavioral effect;
- local repository-policy wording with no runtime consequence.

Budget:

- primary or one producer pass;
- deterministic checks only;
- zero reviewers by default, at most one when scope or reference integrity is
  uncertain;
- no architect and no repeat round.

### M1 — local implementation

Examples:

- one-responsibility bug fix with already known intended behavior;
- an implementation slice of an existing Authoritative gate;
- a local refactor with bounded call sites;
- a focused test addition without changing the contract.

Budget:

- one `implementer` pass;
- one relevant reviewer;
- one repair pass;
- a second reviewer only when the diff changes two genuinely independent risk
  domains.

Typical reviewer choice:

- exact design conformance: `spec_auditor`;
- semantic/root-cause correctness: `compiler_referee`;
- sibling/public/test surface: `regression_auditor`;
- material hot-path/resource effect: `performance_auditor`.

### M2 — contract or cross-layer change

Examples:

- a change crossing parser/HIR/types/core boundaries;
- public API or test-contract change;
- a new cache/invalidation rule;
- a broad module split or shared infrastructure extraction;
- a behavioral change with several sibling entrypoints.

Budget:

- `architect` only when the decision is not already resolved;
- one `implementer` pass;
- at most two reviewers in one round;
- at most two review/repair rounds.

Choose the two reviewers that cover the changed risks. Do not add a third merely
for reassurance.

### M3 — critical certification

Examples:

- new language semantics or public grammar;
- type soundness, ownership, effect, recovery, or IR invariants with broad
  consequence;
- security/authority boundaries;
- persistence or migration correctness;
- release/final-gate certification explicitly requested by the user.

Budget:

- reviewed design and user approval when a new decision exists;
- one `implementer` pass per round;
- at most three reviewers per round;
- at most three review/repair rounds.

If M3 does not converge in three rounds, return to the design or user decision.
Do not keep adding reviewers or measurements.

## Routing reinterpretation

The active matrix in `rules/agent-orchestration.md` is narrowed as follows.

- **Existing Authoritative gate:** normally use `spec_auditor` *or*
  `regression_auditor`, not both. Add the second only when exact conformance and
  sibling/public behavior are both materially exposed.
- **Pure refactor/module split:** normally use `regression_auditor`.
  `spec_auditor` is added only when an Authoritative plan specifies an exact
  topology or zero-change contract that cannot be checked by regression review
  alone.
- **Bug fix:** use `compiler_referee` when semantics, ownership, or root cause is
  the risk; use `regression_auditor` when the cause is established and the risk
  is sibling coverage. Use both only for cross-layer or public behavior.
- **Parser/HIR/type/core work:** three reviewers are reserved for a new public
  contract or M3 invariant. An ordinary implementation gate remains M1 or M2.
- **Performance:** incidental local allocations, branches, or traversals require
  the producer to account for cost, but do not automatically invoke
  `performance_auditor`. The auditor is mandatory only under the risk trigger in
  `rules/performance.md`.
- **Expected output:** pre-write `spec_auditor` remains mandatory. Post-write,
  use one relevant closure reviewer unless the approved contract change is M2
  or M3.
- **Internal progress records:** primary updates them under M0. Do not invoke
  `docs_writer`, code reviewers, broad tests, or a new review round merely for
  bookkeeping.

## Delta review

Fresh reviewer identity does not imply a fresh whole-repository audit.

After a repair, review:

- the accepted finding;
- changed lines;
- direct call sites and dependency cone;
- affected tests, diagnostics, fixtures, or public exports.

Carry forward previously clean areas with no dependency edge from the new diff.
Expand to whole-artifact review only for global architecture, public contract,
shared dispatch, soundness, or release certification.

Every reviewer reports closure scope and uninspected scope. This makes a narrow
review honest without paying for a complete reread.

## Finding batching and round control

- Wait for all assigned reviewers, adjudicate their findings, then send one
  repair bundle to one fresh `implementer`.
- Do not start one implementer session per finding.
- Minor findings may be closed with a reason.
- A minor-only textual/test-comment repair that changes no semantics can close
  with primary diff inspection and focused deterministic checks.
- A heavier finding in the next round signals divergence. Revisit the repair or
  design instead of increasing the panel.
- Exceeding the mode's reviewer or round budget requires a written statement of
  what new decision the extra work can resolve.

## Verification budget

- Run focused checks per gate.
- Run workspace-wide or otherwise broad checks once at the coherent phase/final
  boundary, not after every small gate, unless shared infrastructure changed in
  a way that specifically requires it.
- Do not rerun an unchanged expensive suite after record-only or comment-only
  updates.
- `rules/testing.md` controls command safety; `rules/performance.md` controls
  measurement counts and runtime budgets.

## Progress-record ownership

The primary agent owns repository-state synchronization. Before calling a
coherent gate or task complete, it updates as applicable:

- `tasks/current.md`: current objective, completed/active gate, immediate next
  action, blockers, and known residuals;
- `notes/progress/`: durable completion history for a phase or substantial
  investigation;
- the governing design record or design index when implementation status,
  approval, or supersession changed;
- review/finding records when the task has one.

The implementer should report the proposed record delta, but the primary agent
must ensure it is actually written. Record updates are M0 and do not trigger a
new code-review panel or broad verification. If synchronization is intentionally
deferred, the final report names the exact path and reason.
