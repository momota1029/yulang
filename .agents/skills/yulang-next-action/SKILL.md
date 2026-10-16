---
name: yulang-next-action
description: Consult Yulang's resident task dispatcher at every next-action boundary during the active research loop, including ready work, results, blockers and restart. Route mutual proof/implementation TODOs and choose concrete progress; outside the loop use bounded selection when needed.
---

# Consult the Yulang task dispatcher

This invocation loop belongs to Luna. Delegated workers return evidence/TODOs
to their delegator; they do not recursively invoke a dispatcher or start a trio.

Read `notes/design/2026-10-16-resident-research-loop.md`,
`notes/design/2026-10-16-resident-loop-operations-addendum.md`,
`notes/design/2026-10-16-implementation-first-dispatch.md` and
`tasks/agent-loop/README.md`. For the authorized resident loop, this consultation
is mandatory before every new substantive action/packet and after a result,
blocker, review, changed decision/dependency or restart, including before a wait
or finish decision. It is not limited to times when Luna is unsure. Routine tool
calls inside an already selected bounded packet do not trigger another round.
Outside that loop, use a bounded selection only when useful. A request only to
plan remains read-only and does not authorize dispatching implementation.

## Prepare one bounded evidence packet

Read applicable authority, orchestration budgets and the original gate. Resolve
branch/HEAD, dependency hashes, current objective, latest frozen result and actual
running/ready assignments. Read summaries and precise bounded source sections; check relevant prior
implementation, tests, path history and accepted/rejected proof attempts.
Each new substantive packet identifies which earlier result to reuse or why
its premises no longer apply; do not dump whole histories. Apply question-board freshness and top-level
inference principles before older recovery or proof clauses.

Read `.codex/agents/next-action-selector.toml` and its registration. Reuse the
resident dispatcher identity through supported send/resume tools; do not spawn a
fresh selector for every result. For first launch/replacement, use Sol/high and
`fork_turns: "none"` when supported. Grant only the exact board file as a write
lease, or no writes for a plan-only task. Actual role/model metadata must be
reported separately from requested settings. Follow the canonical capacity and
unsupported-interface fallback, without nested CLIs or fictional workers.

Supply latest implementation and proof progress, immutable inbox IDs/hashes,
current leases, actual review/integration receipts, resource bounds and prior
attempts at unchanged premises. Ask what Luna should do next and what BOTH
producer lanes should work on. The dispatcher may propose a new implementation
task from inspected progress even when neither worker requested it.

## Require an executable routing decision

The answer states the next Luna action, both lane states, selected packet IDs,
priority/dependencies and roles, original gate and first missing premise,
source/consumer owners, frozen inputs and proposed output/inbox paths,
discriminating evidence, acceptance criterion, verification/resource owner and
stop condition. Proposed leases require Luna's validation. An existing safe
running packet may CONTINUE while an idle lane receives a successor.

An idle implementation lane plus authorized ready code work MUST yield an
**implementer Luna/high** assignment now, never Sol, not another all-proof planning round. Run proof
alongside it on independent stable inputs. Preserve genuine proof-dependent A/B
gates; minimal reversible source-evidence construction stays explicitly
provisional. Do not weaken accepted semantics, narrow quantifiers, or mistake
conditional mathematics/tests for source/production closure.

For repeated unchanged premises, require a different method, input or owning
construction that can supply missing evidence. Resolve dependency cycles with a
bounded construction/proof/evidence task or an exact authority question. Do not
invent work to keep a lane busy. Apply evidence-backed bounded Astra escalation
only under the resident-loop contract.

## Implementation-ready audit and research-only escape

A blocked N1/source theorem is not a proof that every independent code target
is blocked. When no implementation has run across two research-only checkpoints,
inspect at least two distinct approved code owners and emit an executable
Luna/high code/verification/provisional-evidence packet, or NO_SAFE_CODE_SLICE
with a concrete reason at each inspected owner. Do not pick a third similar
conditional proof by default. A new narrow test for already approved behavior
does not require new semantic approval; altering test expectations or shipping
proof-dependent mechanics does. Record concrete changed code/test evidence,
not another "implementation should happen" TODO.

## Consume and continue

Luna validates authority, stability, non-overlapping leases and resource bounds,
then performs the chosen dispatch/review/integration. Return an unsafe proposal
with its exact blocker and ask the dispatcher to revise it. Do not silently skip
the dispatcher because work already looks ready. Use `task_decomposer` only when
actual further splitting is needed, not as a mandatory planning pass.

The dispatcher alone writes the leased scheduling board; workers submit TODOs
only in their individual inbox files. Send actual launch, review and integration
receipts back so PROPOSED is never confused with RUNNING or DONE. Keep records
compact. Obtain the next consultation at the next boundary; do not stop the
parent objective merely because one bounded worker finished.
