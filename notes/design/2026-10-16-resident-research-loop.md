# Resident implementation / proof / dispatch loop

Status: Authoritative for the user's explicit workflow decision
Scope: ongoing research/simple-sub-intrusion orchestration; no compiler semantics
Requested-by: user's explicit 2026-10-16 request to edit subagents/skills and push
Approved-by: that request (three resident Sol roles, Luna consultation, mutual TODOs, bounded Astra escalation, implementation advancement)
Approved-at: 2026-10-16
Drafted-by: repository-maintenance primary
Reviewed-by: no independent runtime reviewer available in the editing environment; static verification recorded separately
Supersedes: 2026-10-12-next-action-selection.md for this loop's cadence, selector mode and model routing; the exact conflicting clauses listed below

## Authority and limits

The selected primary remains Luna. The existing `next_action_selector` becomes
the resident **task dispatcher**; do not start another dispatcher under a new
name. `implementer` and `prover` are the other two resident roles. The dispatcher
chooses work and assigns target roles; Luna executes those decisions after
checking authority, exact leases, dependencies, capacity and required review.
Only the primary starts or maintains this loop; children follow their bounded
role packets and never interpret inherited skills as authority to start a trio.
Safety rejection returns the concrete reason to the dispatcher for a revised
choice. This is not permission for Luna to select unrelated work without asking.

This decision overrides, only for the active loop:

- `AGENTS.md` and `rules/agent-orchestration.md` clauses saying selection is
  occasional, read-only, unnecessary for ready work, or not after every result;
- their historical selector Sol/medium and implementer Sol/low pins, and the
  restriction of eligible Astra reasoning escalation to proof work alone;
- the default no-automatic-producer activation in `rules/orchestration-budget.md`:
  three resident roles are the baseline, not an extra reviewer panel;
- primary-only *scheduling-board writes* in `rules/git-concurrency.md` and
  orchestration rules, solely for the explicitly leased board below;
- the prover's shared-task-file ban solely for its exact leased inbox file.

Everything else remains: original A/B proof obligations, natural Simple-sub
behavior, semantic approval, honest proof status, independent certification,
question-board ownership, primary-only Git, exclusive writers, bounded resources
and review budgets. `task_decomposer` remains an optional splitting specialist,
not a second scheduler or a mandatory fourth resident role.

## Resident means event-driven continuity

During an authorized work session keep one dispatcher and one useful owner for
each producer lane. Reuse a healthy worker with the runtime's supported message/
resume mechanism. After packet completion, failure or a blocker, obtain the next
assignment instead of retiring the lane and waiting for another user prompt.
Bound each assignment and reclaim exhausted workers safely. Continuity does not
mean an unbounded model invocation, a polling-only busy loop, or three workers
literally computing every instant. A waiting worker is WAITING, not RUNNING.

No executable task means an honest blocked/waiting state with its missing input,
not artificial notes or additional probes. Stop/pause when the user requests it,
the authorized objective completes, a real decision/external dependency blocks
all useful work, or the actual runtime/resource budget is exhausted. Preserve
checkpoints and exact resumption conditions. These files do not launch a daemon,
keep a closed Codex session alive, or prove workers have been started.

At startup/restart/compaction, reconcile actual identities and leases with the
previous handoff and `tasks/research-lab.md`; historical RUNNING rows are not
runtime evidence. Adopt valid existing lanes instead of spawning duplicates.
Unknown live writers retain their leases until cessation is established. Do not
steal files from a worker merely because its last message is old.

## Luna's consultation loop

Before the first substantive action and every next-action boundary, consult the
resident dispatcher with the latest frozen evidence and current state. Mandatory
boundaries include a producer result or blocker, review/repair outcome, changed
user decision or dependency, restart/worker exit, assigning a new packet, and
deciding to wait, stop or report the goal complete. Ask what Luna should do next
and what each producer should work on. A packet may authorize a bounded sequence
of reads/edits/checks; no per-tool-call consultation is required within it.

A dispatcher decision can assign implementation and proof in parallel, keep an
existing safe packet running, route independent review through Luna, request a
bounded audit, or identify the exact decision blocker. Luna may first perform
necessary emergency cancellation or lease-safety action, then consult with that
result. Do not interrupt useful running work just to make a planning round.
Coalesce already-arrived events into one bounded consultation; never wait for
all producers to finish before refilling an idle lane.

Each decision includes the next Luna action, both lane states, selected packet
IDs, baseline/dependency hashes, actual/proposed worker identities, original
gates, acceptance evidence, precise output leases proposed to Luna, verification
owner, resource limits, stop conditions and the next consultation trigger.
Luna sends the authorized packet and records actual tool acknowledgements.
A proposed role, successful config parse, or launch request is not a worker ID.

## Mutual TODOs and single-writer ownership

The compact scheduling state is `tasks/agent-loop/board.md`. Luna grants its
exact lease to the dispatcher and does not edit it concurrently. The dispatcher
can propose a new task from inspected implementation progress without waiting
for either producer to request it. Only Luna grants actual output leases and
sets review/semantic/integration authority. Actual permissions are inherited
from the parent session: role-local sandbox settings do not establish a write
sandbox or enforce path leases. Inspect effective permissions before dispatch.
If writes are unavailable, report that limitation and return the same TODO/board
deltas in messages without pretending files were edited. The board records those receipts;
it is not a new proof-status authority.

Each producer packet includes one unique exact inbox path under
`tasks/agent-loop/inbox/`, allocated by Luna before dispatch. Both producers can
add proof and implementation TODOs to their own file. No worker writes another
producer's file or the board; no wildcard directory-wide lease is implied.
Follow the fields and handoff protocol in `tasks/agent-loop/README.md`. The
producer freezes a submission and sends its request IDs and content hash through
Luna. The dispatcher acknowledges intake by ID/hash, merges/deduplicates and
routes the tasks. An inbox request alone never assigns another worker work.
Only after acknowledgement may its owner append a new revision; the dispatcher
reads frozen content, never a moving shared file. Preserve prior receipts.

Luna sends launch, cancellation, review and integration receipts to the dispatcher
so the board reflects actual state. Freeze/acknowledge the board and artifacts
before Git integration. A dispatcher restart receives the board lease only after
the old writer stopped. Inbox files are operational records, not substitutes for
theorem notes, `tasks/current.md`, required progress records or approval bundles.
Do not create a second detailed historical task ledger. Existing semantic records
remain authoritative; seed the new board from reconciled live evidence rather
than copying old claims of running workers.

## Keep implementation advancing without manufacturing proof closure

At EVERY consultation inspect current implementation progress as well as open
proofs. If the implementation lane is idle and an authorized ready slice exists,
assign it in that decision. Do not starve it behind optional characterizations,
repeated conditional proofs or bookkeeping. After a completed slice, inspect the
next owning constructor/consumer, integration path or focused regression and
supply an executable successor. When both lanes have stable independent inputs,
run them concurrently; a review on one artifact does not freeze unrelated work.

A genuine open A/B premise blocks only the implementation depending on it and
its production/cutover promotion. It does not block independently justified
implementation. Where proof needs actual source evidence, select the smallest
bounded, reversible, explicitly provisional construction/instrumentation slice;
record the falsifier and keep its production gate OPEN. A TODO cannot itself
authorize semantics or a broad proof-dependent rewrite.

If the lanes wait on one another, identify the dependency cycle and first
missing source-owned premise. Choose a construction-directed proof, a minimal
provisional evidence slice, a distinct method, or the existing authority path.
After two materially different attempts leave the same premise unchanged,
require a new method/input/owner or a localized escalation, not a renamed task.
Missing definitions can be explicit constructive tasks; listing them again does
not discharge the original goal. Tests and conditional lemmas never close an
unproved theorem, and packet completion never silently closes its parent gate.

## Sol and bounded Astra routing

`.codex/config.toml` retains Luna/high and sets the normal child defaults to
`gpt-6.1-sol` / `high`. All three resident role files omit model/effort pins, so
supported native overrides can take effect without editing configuration. Every
normal launch explicitly requests Sol/high when the live schema supports it;
this also prevents Astra descendants inheriting the escalation model. Do not
infer actual execution from model names in prose.

Any of the three roles may request Astra for a concrete localized reasoning
bottleneck after Sol has supplied evidence: an original proof obstruction,
a difficult implementation/semantic invariant, or unresolved dependency/routing
conflict. Luna authorizes one narrower assignment with the prior attempt,
decisive question, exact lease, budget and stop condition, using native
`gpt-6-astra`, normally `low`. Medium/high requires a concrete unresolved point;
xhigh or above follows the existing explicit-request/evidence gate. At most one
Astra escalation is active in this loop, and at most one per decision point
without materially new evidence or explicit user direction. It replaces/suspends
the affected owner after handoff or uses a disjoint read-only question; never
create two writers of the same lease. Return to a verified Sol assignment after
adjudication. Astra is not a standing fourth lane or a broad implementation pass.

Keep the existing global ceiling of 12 and account for all specialists and
proof-coordinator leaves. Reserve room for required independent review. If the
observed ceiling is lower, reduce optional work first; preserve logical roles
and serialize only what the runtime truly cannot run in parallel. All supported
`spawn_agent` calls explicitly use `fork_turns: "none"`. Only the existing bounded
proof-coordinator exception permits child delegation; the dispatcher never spawns.

For temporary capacity errors use the existing initial attempt plus at most two
identical retries. An unsupported role/parameter is not capacity pressure: use a
supported equivalent worker carrying the full role/lease contract immediately.
Do not retry an unsupported interface indefinitely. If native model override is
unsupported, keep Sol, record the limitation and return an exact escalation
packet; do not claim Astra ran. If no subagents are exposed, Luna follows the same
logical dispatcher/producer contract serially and explicitly records degraded
mode, not three running agents or independent self-review. Do not launch nested
CLIs, change unrelated settings, bypass limits or claim unverified hot reload.

## Activation and verification boundary

A plan/status-only, question-answering or workflow-maintenance task remains within
its explicit scope; it does not start compiler implementation merely because
these instructions exist. New sessions load project instructions/configuration;
existing sessions must reread the workflow and reconcile workers, and may need a
restart for configuration changes. Never assume a running worker changed model.
Static validation checks file syntax, registration, references and this contract;
a live smoke check must separately record worker IDs, effective settings,
consultation, both TODO directions, reassignment and clean lease handoff. Do not
report that smoke check as passed without actual tool evidence.

Implementation references (official documentation checked 2026-10-16):
[custom agents and model precedence](https://learn.chatgpt.com/docs/agent-configuration/subagents),
[AGENTS.override discovery](https://learn.chatgpt.com/docs/agent-configuration/agents-md),
and [repository skills](https://learn.chatgpt.com/docs/build-skills).
These describe the harness, not evidence of the user's live session settings.
