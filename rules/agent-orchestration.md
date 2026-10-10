# Codex-only agent orchestration

Yulang uses a primary Codex agent for user interaction, authority resolution,
task classification, adjudication, and Git integration. Keep the user's primary
selection (normally Luna), with bounded specialists for the named risks below.
`rules/orchestration-budget.md` controls activation, reviewer counts, convergence,
verification and measurement budgets. This file defines responsibilities, not a
second mandatory panel. `rules/design-authority.md` controls product authority.
[`research-lab.md`](research-lab.md) controls proactive producer parallelism,
method diversity, dependency-scoped scheduling, and compute coordination.

## Primary responsibility

The primary identifies the target branch, authorized outcome, governing source,
and lightest sufficient M0–M3 mode. It selects bounded assignments, keeps reviewer
reports isolated, adjudicates evidence, batches accepted repairs, and owns user
questions, progress-record synchronization, staging, commits, PRs, and pushes.
The primary owns delegation. A `prover` may dispatch/contact its own leaf workers
only under the proof-coordinator exception below. Other children execute their
assigned role and recommend handoffs; no child inherits authority, independent
review assignment, user approval, or Git duties.
The primary normally keeps independent ready research packets running rather
than executing every investigation itself. Maintain a small ready/running/
review/blocked queue and refill useful capacity after a result arrives. A
blocked semantic question pauses its dependent packets, not the entire lab.

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
| `implementer` | workspace-write | implement confirmed design or accepted findings on leased files |
| `task_decomposer` | read-only | locate the critical path and return a small dependency-ordered set of executable packets; no scheduling or status changes |
| `prover` | workspace-write | construct proofs and exact source-to-proof bridges on leased research paths; bounded proof coordination only when assigned; no self-certification |
| `researcher` | workspace-write | complementary counterexamples, checkers, bounded prototypes and source/artifact evidence on leased research-only paths; no semantic adoption or self-certification |
| `theory_curator` | workspace-write | synchronize leased theory maps after meaningful adjudicated changes; no new proofs or semantic decisions |
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

`prover` deliberately omits both model and effort pins: ordinary proof work
inherits the configured GPT-6.1 Sol/high defaults, while an eligible explicit
Astra spawn can actually override them. `task_decomposer` pins GPT-6.1
Sol/medium for bounded read-only planning. The two roles do not replace the
primary, `architect`, or the independent `compiler_referee`.

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
localized a concrete critical proof obstruction or a semantic bottleneck with
material silent-failure or blast-radius risk, and a cheaper exact lookup,
deterministic check, focused measurement, or
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

## Proof delegation and decomposition

Authority: the user's 2026-10-10 request for Sol proof/task-decomposition roles,
including proof parallelism and Sol-to-Astra escalation. This is the only
exception to the ordinary child-delegation prohibition. It does not transfer
semantic decisions, primary-owned records, Git, or independent certification.

Use `task_decomposer` when several open obligations, a changed premise, or a
stalled critical path need concrete separation. Its read-only result contains
two to four useful packets, the real dependency order and the next decisive
evidence. Each packet fixes the claim, source/baseline, hypotheses, method,
falsifier, proposed output lease, verification/resource budget and stop condition.
Distinguish necessary premises from optional sufficient routes. The primary
validates leases and dispatches ready packets without making another planning
pass a prerequisite. Repeat decomposition only after material evidence,
authority, or critical-path changes; renaming/reclassifying gates is not proof
progress. Small already-specified tasks do not need this role.

Use `prover` for a named constructive obligation; use `researcher` for a
complementary falsification, executable experiment or source audit. Preserve
Simple-sub's ordinary generation, accumulation, propagation, levels, extrusion,
intrusion and generalization. Do not require each constraint to be solved at
generation time, collapse distinct residual lineages, assume the missing
source correspondence, or weaken the theorem to make an unresolved gate close.
Return a derivation with original quantifiers and explicit hypotheses, a genuine
counterexample, or the exact reduced premise with failed routes and next evidence.
Tests of a supplied finite model do not prove its source assumptions.

A `prover` is a leaf unless the primary explicitly assigns a **proof-coordinator
packet**. The primary may grant this packet under the current user authorization
without asking for approval again. It must specify:

- one fixed theorem/gate and governing baseline, allowed reads and exclusions;
- the coordinator's own outputs and preallocated, disjoint leaf-output leases;
- allowed leaf roles (`prover` or `researcher`), model/effort choices, aggregate
  agent/process/CPU/RAM/time limits, and stop/reclaim conditions;
- a child limit of at most **two active leaf workers**, with no further
  delegation, and the evidence required for any Astra leaf.

The coordinator may start complementary methods or genuinely independent
lemmas as soon as their inputs are stable. It may not create a new lease,
expand a theorem's assumptions, appoint reviewers, alter another lane, or give
a leaf coordinator rights. It contacts only its own leaves and the primary.
Leaves receive the original authority plus their narrower task, explicitly
`leaf-only` delegation, and `fork_turns: "none"`; they cannot spawn workers.
The coordinator itself remains a producer and cannot certify its team's work.

Count the coordinator and every descendant in the primary's existing lab
budget. The usual four-to-six useful assignments and configured ceiling of
12 remain unchanged; the observed runtime ceiling takes precedence. A nested
team does not receive another full quota. Preserve room for integration and
fresh closure review. Do not duplicate an existing lane's proof or experiment.

Normal proof leaves explicitly request `gpt-6.1-sol` / `high`, including when
their parent happens to run Astra. For Astra, use the unpinned `prover` role
with a real native `model = "gpt-6-astra"` and explicit effort, normally `low`.
Include the localized Sol argument, precise remaining obstruction, decisive
question and stop bound. At most one Astra leaf is active per coordinator;
it consumes one of the two leaf slots and obeys the per-decision budget above.
A changed model starts a new bounded assignment; it does not mutate the model
of an already-running Sol worker. Record requested and observed settings.

### Proof-dispatch liveness and runtime fallback

For a substantive open proof/semantic bridge with stable premises, the primary
allocates an actual constructive proof packet and exclusive research-note lease
while independent implementation proceeds. Native `prover` is preferred; an
unavailable agent name must not cancel the theorem or become a mandatory setup
or re-planning task. No additional user command is required to try the lane.

1. Inspect the actual `spawn_agent` interface and attempt the registered
   `prover` at most once per session when available. Launch success means an
   actual returned worker identity, **not** a valid TOML file, a prompt naming
   `prover`, a CLI exit status, or a past session's successful launch.
2. On `unknown agent_type`, unavailable custom roles, model/effort override
   rejection, or another runtime routing failure, immediately use a
   runtime-supported generic worker with the exact proof task, governing
   baseline, output lease, and the applicable instructions from
   `.codex/agents/prover.toml` supplied in its task packet. Use only role and
   model options actually supported by that spawn interface; request Sol/high
   when supported, otherwise record the effective choice as unknown. This is
   a **prover-equivalent generic worker**, not an observed custom `prover`.
3. If *no* agent spawn is supported, the primary continues the same constructive
   proof/source audit itself and returns the derivation or the precise missing
   premise. A routing error alone cannot justify `blocked`, `done`, or a
   proof-status promotion. Do not keep trying equivalent failed spawns.
4. Record attempted and actual identities, requested/observed model/effort,
   artifact/proof status, and the specific runtime limitation. Freeze all
   outputs before assigning a fresh independent `compiler_referee`; fallback
   does not relax source reachability, semantics, budgets or review isolation.

All eleven project roles are declared in `.codex/config.toml`; in some CLI
versions project-local declarations are not registered when the runtime's role
table is built. For a **fresh standalone CLI invocation**,
`tools/codex-prover.sh '<proof obligation>'` explicitly supplies the same
role registrations through `-c` overrides. This is an optional diagnostic
and proof entry point, **not** a reason to launch a nested Codex process from
an already-running team or to halt in-session fallback. It does not prove
that a tool-backed runtime supports named roles or Astra overrides.

Do not bypass runtime limits, change a role's pin to fake a model switch,
invent configuration keys, claim Astra ran, or retry an unavailable route.
Continue feasible proof work and report genuine mathematical blockers separately.

Report each child's identity, role, effective settings when observable, lease,
dependency and state to the primary's queue. Release a leaf's outputs only
after its writes have stopped. Before handing the assembled proof to review or
Git integration, freeze all contributing outputs and stop or reclaim every
contributing leaf lease. A blocked/cancelled coordinator returns its live leaf
identities and leases to the primary. A subtree is not finished while a leaf
may still write. The primary assigns a fresh `compiler_referee` to the frozen
proof; coauthors and their proof coordinator are ineligible for that review.

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
most two; M3 at most three, per coherent artifact. These are not producer or
whole-goal concurrency limits. The expected-output pre-write gate is retained.

| task | pre-write | producer | review selection under the budget |
|---|---|---|---|
| file/symbol/current-state lookup | primary or built-in `explorer` | — | none |
| read-only root cause | focused exploration; `architect` only for unresolved design | — | `compiler_referee` for difficult semantics |
| multi-gate research or unclear critical path | `task_decomposer` only when concrete separation is needed | primary dispatches ready packets; no automatic repeated planning | no proof/status promotion from a plan |
| open proof/conjecture or production bridge | freeze statement, source assumptions and exclusions | `prover` for construction; complementary `researcher` packets and read-only source work; bounded proof coordination when assigned | fresh `compiler_referee` for closure; add `spec_auditor` only for a distinct conformance risk |
| exhaustive/differential/mutation experiment | named hypothesis, independent oracle scope and resource envelope | `researcher` on unique research paths | review the model's assumptions and independence, not only green counts |
| theory status/supersession/dependency change | adjudicated result and exact evidence | `theory_curator` on leased maps | M0 synchronization; disputed mathematical implication returns to review |
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
owner, budget, and stop condition. Research packets also name the method,
expected falsifier, dependency version, output lease, and promotion boundary;
use the compact packet in `rules/research-lab.md`. Prefer exact locators over full
chat histories and raw logs; retain all necessary semantic assumptions.

Every native spawn explicitly uses `fork_turns: "none"` when the schema supports
it. If the runtime cannot isolate history, report that boundary instead of
claiming independence. Child spawning is limited to the proof-coordinator
exception above. No child may change model policy, ask the user to approve its
packet again, or perform Git integration.

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

Keep reports of reviewers assigned to the same frozen artifact mutually hidden
until they finish. Producers may work concurrently under explicit disjoint-file
leases or in separate worktrees, as specified in `rules/git-concurrency.md`.
Reviewers read a pinned revision or frozen artifact/dependency snapshot, not a
moving live diff. A different research author is not automatically an independent
reviewer of a result they helped construct. Preserve role permissions regardless
of model. The question-board workflow remains primary-only; research children
neither edit its answer bundles nor acquire Git rights.

`task_decomposer` proposes packets, not new semantics, leases or live workers.
`prover` follows the proof contract above; all leaf reports return through their
delegator for primary adjudication. `researcher` may explore an explicitly
labeled candidate or added hypothesis without adopting it. Production code
remains the `implementer`'s confirmed-scope
work; a research packet does not authorize bypassing existing inference gates.
`theory_curator` receives accepted conclusions and locators, never authority to
promote a bounded probe to a theorem. Neither role edits another worker's files,
spawns children, changes model policy, or integrates Git.

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
the primary, through the assigned proof coordinator for a leaf in that subtree;
other cross-role contact remains primary-owned. No raw transcript is required.

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
