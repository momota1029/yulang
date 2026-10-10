# Parallel research laboratory

Effective: 2026-10-05. Authority: the user's explicit request to increase
subagent parallelism and operate Yulang research as a small laboratory.
Scope: research scheduling and safe collaboration, not language semantics,
proof status, supported inputs, model escalation, or production adoption.

This policy separates **research throughput** from **review-panel size**.
It supersedes the former blanket read-only-parallel / one-child-writer rule
only through the disjoint-file protocol in `git-concurrency.md`. M0–M3 review
budgets, independent certification, question-board approval and primary-only
Git integration remain in force. Do not use parallelism to bypass a proof or
implementation gate.

## Dispatch early, with different methods

When two useful tasks have independent inputs and safe output ownership,
parallel dispatch is the default. Do not wait for a task to become M3, for a
first attempt to fail, or for the user to request each additional worker.
Do not split trivial M0 work merely to fill seats.

For a sustained multi-gate research goal, normally keep **four to six useful
assignments active in total**, counting producers, reviewers and curation.
Count a proof coordinator and all its leaf workers in that same total.
Prefer three or four substantive producer/method lanes plus the specific
review or reconciliation that can unblock them. A critical conjecture or
bridge normally gets complementary attacks in the same wave:

- a constructive proof or derivation, with its exact hypotheses;
- a counterexample, mutation or bounded exhaustive search;
- source/legacy/implementation correspondence, testing whether those premises
  actually follow from the selected contract and retained artifacts.

These are different questions, not three copies of the same prompt. A bounded
scope or shared-authority prerequisite may make fewer workers appropriate;
record that concrete constraint once and proceed. Ready work can be drawn
from another gate while the current gate awaits a result or user answer.

The configured session ceiling is **12**, not a utilization target. The primary
may temporarily use up to ten active assignments for a named ready backlog
when runtime capacity, rate allowance, CPU/RAM and integration bandwidth permit.
Keep headroom for a decisive review or blocker investigation. Respect the
observed runtime ceiling if it is lower, including its treatment of the parent.
Do not invent tools, successful spawns, hot reload, role availability, or model
overrides. If parallel agents are unavailable, do the feasible bounded work
and report the limitation; a primary reread is not independent review.

The existing primary and specialist model/effort pins stay unchanged. New
research roles inherit configured defaults unless their role files pin a key.
More parallel workers do not authorize more expensive model tiers. Astra
escalation still follows `agent-orchestration.md`.

## Primary as coordinator and integrator

At startup, inspect the current task, governing sources, active handoffs and
actual worker/resource capacity. Use the runtime plan or a short primary-owned
queue, not a new scheduling framework. Each job needs only:

`id | gate/method | baseline | owner | write lease | dependency | state | next evidence`

Use `task_decomposer` for a bounded packet proposal when the critical path needs
clarification; dispatch already-ready work while it runs. Route constructive
proofs to `prover` and complementary falsification/experiments/source audits to
`researcher`. A primary-assigned proof coordinator may dispatch its own leaves
only under [the bounded exception](agent-orchestration.md#proof-delegation-and-decomposition).
Keep descendant identities, leases and resource use visible in the same queue;
task decomposition and proof coordination do not create a second primary.

Use `ready / running / review / commit-ready / blocked / done / superseded`. These are observed
states: a proposed lane is not running until a launch actually succeeds.
`tasks/research-lab.md` is an inference startup seed, not proof of running workers.
Persist the compact queue at coherent checkpoints or handoff, not after every
tool call. Keep transient traces and timing noise out of shared status files.

Dispatch ready packets before a long primary-local investigation. The primary
keeps authority resolution, integration and critical-path decisions; it can do
bounded unassigned work while children run, but must not duplicate their tasks
or become the sole author of every proof, probe, test and status note.

After any completion/blocker, adjudicate the report and refill useful capacity.
Do not wait for all lanes to finish before reviewing one frozen artifact or
starting another independent calculation. A review/repair barrier applies only
to that artifact and its dependency component. Batch its findings once; do not
start one repair worker per finding or restart clean unrelated reviews.

## Commit conveyor and two-phase integration

Parallel research must not accumulate indefinitely in the working tree while
waiting for unrelated curation or theorem-map reconciliation. A frozen,
self-contained research artifact may enter `commit-ready` and be checkpointed
before shared status records are synchronized.

The primary may immediately commit and push a research-only checkpoint when all
of the following hold:

1. The exact changed paths are under one completed lease and are research-only
   artifacts such as a unique `notes/progress/` note or `tools/research_*`
   checker. The checkpoint does not modify production code, authoritative
   semantics, public grammar/API, expected outputs, manifests/lockfiles,
   `questions/`, `tasks/current.md`, `notes/design/INDEX.md`, or other
   shared coordination files.
2. The artifact is frozen, its baseline and direct dependencies are rechecked
   against current HEAD, and unrelated branch movement does not invalidate its
   assumptions.
3. Its status is honest in the artifact and report: e.g. exploratory,
   characterization, conditional derivation, or unreviewed research checkpoint.
   A checkpoint must not claim independent review, theorem closure, production
   conformance, or implementation authority that has not occurred.
4. Any executable artifact has its narrow deterministic check recorded, and the
   primary has inspected the exact path list/diff for lease and scope integrity.
5. No accepted blocking/major finding already applies to that exact frozen
   artifact. Review may still be pending if the checkpoint is explicitly
   research-only and makes no reviewed/authoritative claim.

Do not batch unrelated ready artifacts into one commit merely to reduce Git
operations. Drain each coherent artifact independently, preferably as soon as it
becomes `commit-ready`. If two or more frozen research artifacts are waiting,
the primary should drain at least one checkpoint before beginning another long
primary-local investigation or adding more write-producing backlog, unless a
concrete dependency or Git-safety blocker prevents it.

Shared integration is a second phase. `tasks/current.md`, theory maps, design
indexes, reviewed-status promotion, and cross-lane synthesis may follow in
separate commits after adjudication. Those later records refer to the already
checkpointed artifact commit. A later review repair is another focused commit;
it need not rewrite or squash the honest research checkpoint.

This fast path is not available for production implementation, test-contract
changes, authoritative design/semantic changes, question-board bundles, shared
configuration/policy, or any artifact whose safe interpretation depends on
simultaneously updating a shared contract. Those keep their existing review and
integration gates.

## One semantic baseline, explicit dependency invalidation

Every packet names a commit or frozen file hashes, exact governing sections,
and the user's relevant decisions/corrections. The primary resolves authority;
workers do not independently choose what the language means. A candidate
assumption may be explored when explicitly labeled, not silently promoted.

Keep established results and failed routes in the packet. Read the original
source when an index summary is insufficient. In particular, `'e?` means
stopping handler protection for `'e`-derived effects leaving the marked slot;
it is not optional membership, may-flow, or a provenance edge. Do not infer a
particular legacy pop count, new carrier, or handler-selection rule from that
sentence alone; derive the correspondence rather than inventing it.

When a user correction or accepted result changes a premise, notify only the
workers whose dependency cone uses it, mark their affected output superseded,
and supply a revised packet. A superseded success is not evidence for the new
contract. Before integration, recheck dependencies against the current branch;
unrelated commits do not require a whole-repository reread or blanket restart.

Question-board publication blocks only dependent work. Follow its existing
approval, unchanged-content and questioner-integration rules. Do not let
research workers edit or consume an unvalidated approval bundle as authority.

## Compact assignment packet

Give each worker concise technical English containing:

```text
Job / gate / method:
Baseline and exact governing sources:
Accepted decisions, assumptions, previous results and failed routes:
Question, expected falsifier, and useful output:
Allowed reads / frozen dependencies:
Exclusive write paths / isolated worktree or scratch outputs:
Verification owner, commands, CPU/process/RAM/wall-time limits:
Stop condition and escalation boundary:
Report: claim class, derivation or minimized witness, exact checks,
        changed paths, dependency changes, omissions, next action.
Commit packet: exact leased paths, baseline SHA and changed dependency hashes,
        claim/review status, verification already run, proposed one-line commit
        message, and shared-record deltas intentionally deferred.
```

Use `fork_turns: "none"` whenever the actual spawn schema supports it.
Only an explicitly assigned proof coordinator may re-delegate within the
bounded exception; all its leaves and other children cannot re-delegate.
Children never mutate Git, change model configuration, or ask the user for
decisions. Leaf evidence returns through its coordinator to the primary.
Do not pass producers'
defenses or other reviewers' verdicts to an independent closure reviewer.

## Writes, artifacts and review snapshots

Use the explicit leases in `git-concurrency.md`. Independent new proof notes
and checker files are good shared-tree outputs; simultaneous edits to different
sections of `crates/yu-hir/src/lib.rs` are not. Use isolated worktrees or return
patches for a primary-owned hotspot. Include generated outputs, formatters and
build side effects in the ownership analysis.

Research artifacts remain research-only until their own gate closes. A
`researcher` can write a named draft/probe, not change production routing or
relabel tests as authoritative. A proof constructor is a producer; their
report is not an independent mathematical review. A counterexample coauthor
also cannot independently certify the resulting repaired proof.

Freeze the candidate and relevant dependencies before review. Integrate a
coherent verified slice without waiting for unrelated work, preserving every
other lease and uncommitted handoff. If a target changes after review, recheck
the affected delta; do not certify a moving working tree.

## Parallel calculations without resource multiplication

LLM concurrency and local process concurrency are separate budgets. Inspect
available cores/memory and other active sessions before a compute wave; do not
assume this primary owns all machine resources. Use unique output/log/checkpoint
paths per job and one verification owner for shared builds.

Default to at most **four lightweight single-process probes** concurrently
when their footprint is known to fit, and **one heavyweight Cargo/build/test
process** at a time. Start an unfamiliar expensive search with a bounded pilot,
then partition its input domain by disjoint seed/range with explicit coverage.
Do not give every agent all cores or multiply Cargo builds and target caches.
Separate worktrees do not isolate CPU/RAM. Tighten the budget under contention;
raising it needs an aggregate resource rationale, not merely free agent slots.

Each calculation has a finite input envelope, seed/range, stop/kill condition
and reproducible command. Checkpoint a valuable search before its budget ends.
Do not hide timeouts, killed runs, partial enumeration or uncovered shards.
Larger domains are useful only when they can discriminate a named hypothesis.
Performance timing/repetition retains the separate limits in `performance.md`;
correctness enumeration is not a license for unbounded process spawning.

## Evidence quality and stopping unproductive loops

A useful research result is a proved statement with explicit scope, a reduced
unproved premise, a minimized counterexample, an independently grounded
source/artifact bridge, or a discriminating executable test. Report completed
gates and reduced uncertainty, not lines of notes, commit counts or agent hours.

For an executable claim, state what the reference and candidate share. Two
implementations of the same supplied transition assumptions are differential
consistency evidence, not independent source-semantics validation. Keep finite
characterization, conditional theorem, reviewed theorem and production authority
distinct. Mutation tests should attack named shortcuts rather than tautologies.

After two successive materially different proof/model variants leave the same
main premise untouched, do not launch a third proof variant mechanically. First
apply the proof-obligation-economy classification in
`compiler-engineering.md`: decide whether the premise is cutover-critical
safety/correctness, required natural inference behavior, stronger research
characterization, or reconstruction debt caused by discarded compiler evidence.
For reconstruction debt, redirect a lane toward the owning construction point
and test a canonical retained certificate/invariant before adding another
semantic relation. For stronger characterization, keep the theorem as research
unless current Authority actually makes it a production prerequisite. For a
true correctness or natural-inference obligation, continue with a different
proof method, exact missing source rule, or artifact bridge. This audit never
silently weakens semantics or changes a DAG status.

Do not accumulate larger case counts or another restatement of the same open
gate as progress. Close or repurpose idle/duplicate workers; no polling daemon
or busy loop is required by this policy.

## Curation and handoff

A leased `theory_curator` synchronizes meaningful theorem status, assumptions,
supersession, counterexample scope, production boundaries and dependencies.
Ordinary probe-count increases do not require a new map edit. Keep old results
as historical evidence where appropriate, without using withdrawn semantics
to justify current claims. Disputed implications go back to the primary.

The primary retains `tasks/current.md`, design authority, shared index and
integration ownership. It verifies delegated map edits and records exact
remaining work. No new standing review panel is needed for M0 synchronization.
At handoff, preserve baseline/leases, ready jobs, accepted findings, incomplete
calculations and missing decisions. Configuration changes alone do not prove
an already-running Codex session has reloaded or adopted laboratory scheduling.
