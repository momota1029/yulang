# Git and concurrency safety

## Integration ownership

The primary agent owns staging, commits, branch updates, PRs, and pushes. Subagents report changed paths and checks but do not stage, commit, push, rewrite history, or delete branches.

Stage explicit paths. Do not use `git add -A` in a shared or potentially dirty working tree. Before every commit, inspect the branch, `git status`, staged diff, and whether unrelated concurrent work is present.

Under [`question-board.md`](question-board.md), pending question directories
and unapproved drafts in `questions/` stay unstaged and uncommitted, including
during ordinary checkpoint commits. Do not hide them with Git ignore rules.
The answering primary writes only selected answer files/history and never
mutates Git. All unintegrated bundles, including approved local answers, stay
excluded from ordinary checkpoints. The questioning primary discovers and
validates a finalized local answer, rechecks bundle stability, and alone commits
the matching question, approved current draft and approved answer together.
Check current-file equality with committed versions before consumption. No
worktree-wide writer/Git ownership handoff is required for these disjoint paths.
Exclude other pending questions and unrelated staged work; concrete index/path
conflicts defer only affected integration. Tracked instructions/templates are
infrastructure and may be committed.

## Coherent commits

Prefer one commit per confirmed design gate or coherent cause. Separate:

- behavior from formatting-only drift;
- a bug fix from unrelated cleanup;
- mechanical relocation from semantic change;
- policy extraction from the atomic active-policy switch.

A commit is a reviewable and bisectable checkpoint, not merely a progress timestamp.

### Research-only checkpoint fast path

For the parallel laboratory, a primary may commit and push a frozen,
self-contained research artifact before `tasks/current.md`, theory maps, or
design indexes are synchronized, when the artifact satisfies the
`commit-ready` criteria in `research-lab.md`. This is intentionally a
two-phase flow: preserve the research result first, then integrate its accepted
meaning into shared records.

Such a checkpoint:

- contains only the exact completed lease paths and no unrelated shared-file
  edits;
- records its actual claim class and pending review honestly;
- may be unreviewed only when it remains explicitly research-only and claims no
  closed theorem, production conformance, or authority;
- receives focused follow-up commits for review repairs or curation rather than
  waiting in a dirty tree for unrelated lanes;
- does not satisfy a gate-completion requirement by itself.

The normal requirement to synchronize shared records still applies before a
gate is declared complete or a production/authoritative change is integrated.
Do not squash away a useful honest checkpoint solely because later curation or
review refined its claim.

## Parallel work

Independent producers, experiments, and read-only reviewers may run in parallel.
This user-directed policy replaces the former blanket same-worktree child-writer
ban. It does not permit concurrent writers to one file or several Git integrators.
Use the scheduling and resource budgets in [`research-lab.md`](research-lab.md).

### Disjoint-file mode

The primary may run concurrent write-capable children in one worktree only when:

1. Each has an explicit, non-overlapping lease of exact output paths, plus a
   pinned source/authority baseline and a bounded read/dependency set. Different
   functions or sections in one file are not disjoint leases. Leases are
   coordination contracts, not a claim of sandbox-enforced file permissions.
2. No worker depends on another worker's unfinished edits. Read stable shared
   inputs from the pinned revision or a frozen copy. Generated files, reports,
   temporary output, caches with unsafe writers, and formatting writes are part
   of the write set, not exceptions. Unknown side effects require isolation.
3. `AGENTS.md`, `rules/`, `.codex/`, manifests/lockfiles, `tasks/current.md`,
   `notes/design/INDEX.md`, and the shared lane queue have one coordinating
   primary writer. Theory-map files may have one explicitly leased curator.
   Other workers report proposed changes instead of editing these hotspots.
4. Exactly one primary owns the worktree's index, refs, worktree administration,
   stage/commit/push and integration. Children perform no Git mutation. Distinct
   active primaries must coordinate exact ownership before sharing a worktree;
   the existing question-board handoff remains separate and unchanged.
5. Before review/integration, freeze the leased artifact and its dependency
   snapshot, inspect its complete diff and output list, and run focused checks
   on that exact combination. Revalidate changed dependencies before accepting
   a result. Do not certify a mixed live worktree as a reviewed snapshot.

A primary must not edit a child's leased path until the worker acknowledges
handoff/completion or its writes have actually stopped. Unrelated work remains
untouched. Scope/lease changes are explicit and invalidate only affected results.

The bounded proof-coordinator exception in `agent-orchestration.md` uses these
same primary-granted leases. A coordinator may pass a preallocated path set to
one leaf, but cannot add paths, write a live leaf's files, or transfer Git/shared
record ownership. All descendants remain visible to the primary; a coordinator's
completion or interruption does not release a still-writing leaf's lease.

### Isolated mode and shared builds

Use a separate worktree/branch or frozen scratch copy for alternative edits to
the same file, coupled interface changes, uncertain tool side effects, or reads
that cannot remain stable. The primary creates and integrates isolated outputs;
children still do not commit or switch branches. Do not resolve collisions by
blanket stashing, resetting, cleaning, or overwriting another worker's changes.

Separate worktrees isolate files, not CPU/RAM. Heavy builds are coordinated by
one verification owner by default. Shared manifests, lockfiles, build targets,
and snapshot writers are not independent just because source paths differ.
Allocate unique small experiment outputs; broaden build concurrency only after
an aggregate resource check. Integrate one coherent dependency set at a time,
while unrelated lanes keep working. If safe isolation is unavailable, serialize
only the conflicting write/build seam, not every read/proof/experiment.

## Branch safety

The Codex-only policy on the `yulang3` branch does not authorize changes to frozen `main`. Work on the branch named by the task. Routine pushes of coherent commits to the current working branch are allowed when they preserve the intended remote synchronization; never force-push, rewrite history, or retarget another branch without explicit user instruction.

After final verification and record synchronization, the primary pushes a
coherent current-branch commit by default. Immediately before pushing, resolve
the destination remote/ref and inspect every commit in `<remote-ref>..HEAD`.
Push only when that whole outbound range is intended and coherent; otherwise
defer on the concrete upstream/safety blocker and report it. Do not retarget or
force-push to work around divergence.

When upstream moved, re-evaluate scope before integration. Do not force a ref merely to preserve a local plan.

## Generated and temporary files

Do not commit build output, logs, scratch files, tool state, or unrelated formatting drift. Respect `.gitignore`, but do not use ignore rules to hide a source file that should be reviewed.
