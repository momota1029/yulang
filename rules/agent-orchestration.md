# Codex-only agent orchestration

Yulang uses a primary Codex agent for user interaction, authority resolution,
task classification, adjudication, and Git integration. Keep the user's primary
selection (normally Luna), with bounded specialists for the named risks below.
`rules/orchestration-budget.md` controls activation, reviewer counts, convergence,
verification and measurement budgets. This file defines responsibilities, not a
second mandatory panel. `rules/design-authority.md` controls product authority.

## Primary responsibility

The primary identifies the target branch, authorized outcome, governing source,
and lightest sufficient M0–M3 mode. It selects bounded assignments, keeps reviewer
reports isolated, adjudicates evidence, batches accepted repairs, and owns user
questions, progress-record synchronization, staging, commits, PRs, and pushes.
Only the primary spawns or contacts subagents. Children execute their assigned
role and recommend handoffs; they do not inherit orchestration or Git duties.

Resolve routine choices from the request, Authoritative gate, and repository
before asking the user. A settled implementation does not need approval again.
Stop only work affected by a genuinely missing decision, and continue independent
authorized work. Do not invent approvals, tests, models, or independent reviews.
The primary's reread and a producer's self-review do not count as independent review.

## Roles

| role | mode | responsibility |
|---|---|---|
| built-in `explorer` | read-only | map files, symbols, entrypoints, call paths, and current state |
| `architect` | read-only | unresolved design, invariants, gates, rollback and decisions |
| `implementer` | workspace-write | implement confirmed design or accepted findings |
| `compiler_referee` | read-only | adversarial semantics, root cause, soundness and invariant review |
| `spec_auditor` | read-only | exact design/spec/test-contract conformance |
| `regression_auditor` | read-only | sibling paths, public surfaces, fixtures, diagnostics and parity |
| `performance_auditor` | read-only | work, allocation, cache, parallelism and material resource risk |
| `docs_writer` | workspace-write | confirmed public documentation under artifact style rules |

## Model routing and Astra escalation

Read `.codex/config.toml` and the selected `.codex/agents/*.toml` as the executable
source of model, effort, and sandbox settings. Do not maintain a conflicting tier
table in prose. The current primary is Luna/high; the inspected `implementer`
pin is Sol/low and `architect` pin is Sol/medium. Preserve those intentional
settings rather than replacing them to match old Terra/Sol descriptions.

Choose the role by its deliverable and concrete risk. Sol specialist work does
not make the specialist a second primary. Use the normal configured model first;
length, multiple files, architectural vocabulary, or model rank alone is not an
escalation reason. Historical Level, Fable/Sonnet, or Terra labels are provenance,
not live routing instructions.

Custom role-file model/effort pins override spawn settings. For omitted keys,
resolution is explicit spawn setting, corresponding `[agents]` default, then
parent setting. A model name in the assignment text does not select that model.
Inspect the callable schema and effective runtime metadata when available;
report requested versus observed settings separately. Do not claim that a live
session reloaded changed files or that a requested override actually ran.

Astra remains an exceptional, bounded reasoning escalation only after Sol has
localized a concrete bottleneck with material silent-failure or blast-radius
risk, and a cheaper exact lookup, deterministic check, focused measurement, or
bounded Sol check cannot close it. The new assignment must be narrower and name
the decisive question, evidence, and stop condition. It is not an implementation
worker or an automatic stage of every panel.

Use native model/effort overrides only on a role whose corresponding pins are
absent and whose live schema supports them. A pinned role is not an escalation
path: do not pretend a launch argument overrides it, silently select a different
role, or edit configuration to escape the pin. Keep the configured assignment
and report the specific limitation; a persistent routing change needs its own
authorized scope. This check corrects older prose claiming roles were unpinned.

For an eligible Astra assignment, normally start at low effort. Medium/high
requires a concrete unresolved point; xhigh or above requires an explicit user
request or evidence from a prior bounded attempt. Allow at most one Astra
assignment per decision point by default; another requires materially new
bounded evidence/question or explicit user instruction. Return to the configured
normal roles after adjudication. Never increase cost merely for reassurance.

## Task classification

Before a write, classify authority (`none / existing / new-decision`), behavior
(`none / intended / uncertain`), scope (`local / cross-layer`), performance
(`cold / hot / unknown`), and surface (`internal / public / docs`).

Use `architect` when a required decision or behavior remains unresolved. A
cross-layer implementation of a sufficiently specified Authoritative gate does
not reopen architecture. Re-enter design only for a concrete contradiction,
false premise, missing decision, or authorized scope expansion. This follows the
budget's M2 rule rather than treating `scope = cross-layer` as an automatic gate.

## Routing matrix

The review column lists eligible risk coverage under the selected M0–M3 budget,
not reviewers to start together. M0 normally has zero; M1 normally one; M2 at
most two; M3 at most three. The expected-output pre-write gate below is retained.

| task | pre-write | producer | review selection under the budget |
|---|---|---|---|
| file/symbol/current-state lookup | primary or built-in `explorer` | — | none |
| read-only root cause | focused exploration; `architect` only for unresolved design | — | `compiler_referee` for difficult semantics |
| typo/format/fully specified rename or internal records | — | primary or one producer | M0 deterministic checks; optional integrity review only for a named risk |
| existing Authoritative gate | reuse settled design | `implementer` | `spec_auditor` or `regression_auditor`; both only for independent exposed risks |
| pure refactor/module split | `architect` only if design is insufficient | `implementer` | normally `regression_auditor`; exact topology contract may need `spec_auditor` |
| bug fix | locate cause/owner; resolve any missing decision | `implementer` | `compiler_referee` or `regression_auditor` by the actual failure class |
| parser/HIR/type/core/public API | design and user approval only for new decisions | `implementer` | choose semantic/conformance/regression coverage within M1–M3; no automatic three-person panel |
| performance | focused path evidence and unresolved design only | `implementer` | `performance_auditor` under material-risk trigger; add semantic/regression coverage only when exposed |
| snapshot/golden/expected output | mandatory pre-write `spec_auditor` | `implementer` | one closure reviewer unless the approved change is M2/M3 |
| new/changed design document | `architect` | primary records reviewed draft | compiler/spec review under the budget, then user approval for a new decision |
| public docs/README | `spec_auditor` for semantics/examples | `docs_writer` | conformance; executable examples may expose regression risk |
| repository/orchestration rule | primary; `architect` only for unresolved policy | primary | M0 for wording alignment; fresh `spec_auditor` when actual workflow risk warrants it |

## Information boundaries and assignment packet

Use concise technical English for child instructions and reports. Give the
question/deliverable, revision and worktree, governing sources, allowed reads and
owned write paths, confirmed decisions, non-goals, checks and one verification
owner, budget, and stop condition. Prefer exact file/section locators over full
chat histories and raw logs; retain all necessary semantic assumptions.

Every native spawn explicitly uses `fork_turns: "none"` when the schema supports
it. If the runtime cannot isolate history, report that boundary instead of
claiming independence. No child may spawn another child, change model policy,
ask the user to approve its packet again, or perform Git integration.

`implementer` and `docs_writer` receive confirmed scope, accepted findings, and
direct dependencies. They neither settle unspecified durable choices nor certify
their own output. The primary owns record synchronization unless specifically
assigned; a producer reports the proposed record delta.

- `compiler_referee`: target code, direct dependencies, authoritative source and
  relevant tests, but not the initial producer's defense or success claim.
- `spec_auditor`: exact governing source, target diff and test contract; current
  output and implementation convenience are not authority.
- `regression_auditor`: before/after, public call sites, sibling cases, fixtures
  and diagnostics; do not assume a producer's zero-behavior-change claim.
- `performance_auditor`: changed path, call frequency, loops/worklists, ownership
  and measurements; a producer's performance claim is not evidence.

Keep reviewer reports mutually hidden until all assigned reviewers finish.
Parallelize independent read-only work only. Never run two write-capable agents
in one working tree. Preserve the role's permissions regardless of model.

## Findings and repair loop

Use `BLOCKING` for invalid semantics, missing authority/input, unsafe operations,
or an unexecutable rule; `major` for hidden assumptions, wrong ownership,
contract deviations, likely regressions, or material resource risk; `minor` for
local clarity/organization/coverage with no correctness change.

The primary accepts or rejects each finding with evidence and a reason. Batch
accepted blocking/major findings into one repair pass, then use a fresh reviewer
on the changed lines, direct call sites and dependency cone under the budget.
Do not reopen unchanged clean scope without a global invariant or release reason.
Minor-only repairs follow the primary-inspection exception. Continue only while
rounds close or materially narrow findings; no-progress returns to the precise
root cause or decision, not another identical panel. A reviewer never repairs
and independently approves its own finding.

Completion requires no accepted blocking/major finding in the latest required
review and no subsequent artifact change except permitted record/minor updates
under the budget. Missing runtime checks remain explicitly unverified.

## Expected-output gate

Before changing snapshots, goldens, fixture/diagnostic expectations, semantic
assertions, or test names, `spec_auditor` checks whether the expectation is
authoritative and whether a user-approved contract change exists. Current
implementation output alone never justifies rewriting the expected result.

## Performance trigger

Account for work, allocations, clones, traversals and resource use on changed
paths. `rules/performance.md` decides when materially uncertain hot-path,
asymptotic, concurrency, or heavy-verification risk requires an auditor and
sets the measurement budget. An incidental allocation or branch is not by itself
an automatic extra review. Do not broaden experiments merely for reassurance.

## Handoff contract

Report role/mode; objective and inspected scope/revision; authority; findings or
changed paths; exact checks and results; uncertainty/unread scope; blocker or
user decision; and one recommended next action. A handoff recommendation goes to
the primary, not directly to another specialist. No raw transcript is required.

## Design workflow

A genuinely new durable decision follows architect draft, independent review,
primary adjudication, user approval, Authoritative record, then implementation
and required review. A settled request or approved gate is not a new approval
checkpoint. Model identity and authorship are provenance, never authority.

## Deterministic checks and hooks

Builds/tests are evidence, not reviewer roles. No automatic repository hook is
introduced by this policy. Use focused safe checks under `rules/testing.md` and
broaden only for affected shared behavior or a coherent phase/final boundary.
Do not rerun broad suites after record/comment-only edits. Syntax and prompt
contract checks do not establish model behavior or independent review.

## Git integration

Follow `rules/git-concurrency.md` and the frequent coherent checkpoint policy in
`AGENTS.md`. Only the primary stages explicit paths, inspects the exact diff and
full intended outbound range, and pushes the authorized branch. Preserve
unrelated/concurrent work; never clean it merely to obtain an empty status.
The `yulang3` policy does not authorize changing frozen `main`.
