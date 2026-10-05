# User-directed parallel research workflow

Date: 2026-10-05
Branch: `research/simple-sub-intrusion`
Inspected baseline: `553c72788b9cb3f45e94821b201815891a97a810`
Scope: repository agent policy, role prompts, session concurrency and an inference lane seed
Status: workflow change with deterministic validation; live Codex behavior unverified
Independent review: unavailable in the editing session; primary consistency inspection is not independent review

## Direction and rationale

The user explicitly requested stronger subagent parallelism and operation as a
small research laboratory. The previous root and orchestration rules limited
parallel children to read-only work and prohibited two child writers in one
worktree. The reviewer budgets also used single-producer/repair wording that
could serialize an entire multi-gate goal.

The update makes two ready, independent packets enough to dispatch in parallel,
with four to six useful active assignments as the sustained research target.
The existing `max_concurrent_threads_per_session` setting changes from 6 to 12;
it is a configured ceiling, not a guarantee that the current runtime accepts or
hot-reloads it. Primary and existing specialist model/effort pins are preserved.
New `researcher` and `theory_curator` files follow the existing role-file shape
and inherit the configured defaults rather than adding premium model routing.

## Changed workflow

Research producers, independent closure reviewers and lightweight curation now
have separate responsibilities. Critical gates get different proof,
falsification and source-conformance methods. Review/repair waits are local to
one frozen artifact; the coordinator refills independent work instead of waiting
for a whole wave. Per-artifact M0–M3 reviewer counts do not increase.

Concurrent shared-tree writers require exact disjoint file leases, stable read
inputs, private outputs and one Git integrator. Same-file sections are not
independent leases. Shared manifests, lockfiles, task/index/configuration files
and build side effects remain coordinated. Overlap or uncertainty falls back
to isolated worktrees or a serialized seam, not a blanket research shutdown.

Compute concurrency is separately bounded: at most four known-light probes and
one heavy build by default, tightened under contention. No unlimited search,
recursive agent fan-out, automatic extra Astra use, or repeated broad test panel
is introduced. User corrections invalidate only their dependency cones; bounded
models remain bounded evidence rather than theorem/production authority.

## Validation and limits

Deterministic validation uses exact baseline Git-blob hashes, local diff/scope
inspection, TOML parsing, role/model-pin checks, reference checks on touched
policy and the startup seed, and checks for obsolete blanket writer rules in
the changed active entrypoints. Compiler sources, test expectations, semantic
designs and approval bundles are not changed.

No native subagent runtime was available in this editing session. No independent
review, successful child launch, active-session reload, throughput measurement,
full compiler checkout or Rust build is claimed. The change is not production
inference certification. On the next actual Codex startup, inspect role discovery
and effective thread settings and begin with bounded disjoint work; if the
runtime imposes a lower capacity, report and use it without inventing another
configuration schema.

`tasks/current.md` and `notes/design/INDEX.md` are intentionally not rewritten by
this policy-only task: they are active research-writer hotspots and no theorem
or language status changes here. `AGENTS.md` and `rules/INDEX.md` route to the new
`tasks/research-lab.md` operational companion and canonical laboratory rule.
The research primary should fold any useful scheduling pointer into its next
coherent current-task synchronization; the underlying inference gates remain
unchanged. This is an explicit record deferral, not an unnoticed stale status.

## Rollback and next observation

If measured contention or integration backlog appears, reduce active jobs or
serialize the affected lease/build seam first. A shared-tree ownership violation
requires isolating that worker before further writes, without deleting others'
work. Reverting the configuration ceiling to 6 is a focused operational rollback;
retain useful parallel read/proof work and all semantic/approval safeguards.
Do not claim a speedup until actual critical-path progress and resource behavior
have been observed under the new policy.
