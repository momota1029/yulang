# Development workflow

## Establish current context

Before changing the repository, read only the context needed for the task:

- `tasks/current.md` for the current objective and immediate work;
- `notes/design/INDEX.md`, then the relevant authoritative design section;
- `spec/` when the language contract is involved;
- a relevant handoff note under `notes/` when one exists;
- the current daily record under `notes/progress/daily/` when continuity matters.

Do not reread a giant design document indiscriminately when the index or task identifies the governing section. Do not treat `tasks/current.md` as a design authority.

## Select an operating mode

Before choosing roles, read `rules/orchestration-budget.md` and select M0, M1,
M2, or M3. State the concrete changed risk domains, reviewer budget, and
convergence criteria.
The role matrix lists eligible specialists; it is not a command to run every
listed reviewer.

Use the lightest sufficient mode. An existing Authoritative design normally
removes the need to reopen architecture. Raise the mode only for a concrete
contract, cross-layer, soundness, performance, or public-surface risk.

## Parallel research startup and replenishment

For an open-ended research or multi-gate goal, read `rules/research-lab.md` and
the current `tasks/research-lab.md` lane seed after identifying source authority.
Create a compact dependency/ownership queue and start useful independent packets
before a long primary-local investigation. Two ready independent assignments are
sufficient; a sustained goal normally targets four to six active assignments.
These are producers/experiments as well as reviewers, not a mandatory panel.

Within each lane, keep the order-of-work checklist below. Across lanes, overlap
proof construction, bounded falsification, source/legacy reconciliation, and
already-authorized code work. Review and integration barriers apply only to the
same artifact and its dependencies. When a worker finishes or blocks, adjudicate
its concise report, integrate a verified slice or request one bounded repair,
and refill the ready queue without waiting for unrelated work.

Before dispatch and dependent integration, synchronize explicit user corrections
and valid question-board handoffs. Stop/rebase only the affected packets. A
researcher may record a candidate assumption but cannot turn it into a language
decision or production permission. Read-only reviewers use frozen targets.

## Respect handoffs

A handoff may record confirmed facts, root-cause localization, rejected approaches, forbidden actions, and the next gate.

- Do not restart investigation of a fact marked confirmed or `再調査するな` without new contradictory evidence.
- Do not repeat a rejected approach in the same form.
- Do not violate a recorded forbidden action.
- When evidence contradicts the handoff, preserve both records and explain the contradiction instead of silently overwriting it.

## Scope before execution

Classify the task before writing:

- authority: none, existing, or new decision;
- behavior: none, intended, or uncertain;
- scope: local or cross-layer;
- performance: cold, hot, or unknown;
- surface: internal, public, or documentation;
- operating mode, reviewer budget, and convergence criteria.

Name the intended files, checks, record updates, and stop condition. Do not expand a bug fix into unrelated cleanup, rename, formatting, or abstraction work. One coherent change should correspond to one cause or one confirmed gate.

Warnings emitted by a touched package or direct dependency are not exempt merely
because they predate the active diff. Audit their cause before closing the work.
When the removal is safe and ownership-local, fix it in a separate coherent
commit with focused verification. When it needs broader authority, record the
exact owner and blocker in `tasks/current.md`; do not leave unbounded warning
debt behind a generic "pre-existing" label.

## Order of work

Prefer this order:

1. locate the public entrypoint and owning responsibility;
2. identify the governing design and invariant;
3. establish the smallest coherent scope and operating mode;
4. change the central type/function or owner first;
5. place helpers behind a visible responsibility boundary;
6. check for new rescans, recomputation, allocation, or hidden coupling;
7. add or update focused tests when behavior changes;
8. run the narrow relevant checks;
9. inspect the diff for scope and responsibility clarity;
10. obtain only the independent review assigned by the selected mode;
11. adjudicate all findings and batch accepted repairs into one pass;
12. synchronize progress/design records before completion.

For an authoritative multi-gate plan, each gate is normally a coherent slice and commit. Do not combine later gates merely because the current edit is nearby. Conversely, do not split one gate into several writer/reviewer cycles merely to handle findings one at a time.

## Decision points

A subagent must not ask interactive permission questions. If a necessary decision is absent, it stops the affected work and reports:

- the exact decision;
- why repository evidence does not resolve it;
- available options and consequences;
- work that remains safe and complete.

The primary agent resolves ordinary repository ambiguity and presents only genuine author/user decisions.

For goal-driven Yulang work, route genuine user decisions through
[`question-board.md`](question-board.md). Read the shared board at turn start
and before dependent actions. The board is `questions/` in the worktree
containing the pending question. Keep questions and drafts unstaged and
uncommitted until the questioning primary discovers and validates a finalized
local answer, then commits the matching question/draft/answer together. The
answering primary saves/displays a draft in a separate thread, obtains explicit
approval and publishes the exact finalized answer without Git mutations. Disjoint
file responsibilities require no worktree-wide writer/Git handoff. Recheck bundle
stability before staging; consume only a fresh valid committed handoff whose
current files match committed versions. Ordinary
conversational clarification need not use the board. An explicit board request
also selects this workflow. Posting a question does not pause a goal; continue
independent authorized work. Publication does not notify or resume a goal.

## Progress records

Long or multi-step work reports at meaningful milestones: relevant files found, root cause found, before a write, after a coherent slice, after checks, and on a blocker or scope expansion. Avoid line-by-line narration.

`tasks/current.md` is navigation: current objective, governing design/section, active gate, immediate next action, blockers, and known residuals. Completed gates, long commit histories, test-count chronology, and review detail belong under `notes/progress/`.

The primary agent owns these updates:

- after a coherent implementation gate, update `tasks/current.md` before declaring the gate complete;
- after a phase or substantial investigation, append or create the appropriate `notes/progress/` record;
- when implementation status, approval, or supersession changes, update the governing design record or `notes/design/INDEX.md` as appropriate;
- record explicit deferrals and known residuals at the point they become decisions.

The producer reports a proposed record delta, but a report is not a repository
update. The primary may lease theory-map synchronization to `theory_curator`
after adjudication; it still verifies the result and owns task/design status.
Synchronize meaningful status, premise, supersession, obstruction or production-
boundary changes at coherent checkpoints, not every additional passing case.
Record-only updates are M0 and do not block independent research or trigger a
review panel, broad test suite, or new repair round.

For repeated appends to a daily file, use a unique end anchor such as:

```md
<!-- daily-append-anchor: 2026-08-30 -->
```

Insert before the anchor. Do not anchor an automated patch on generic repeated headings such as `確認:` or `判断:`.

## Dirty working trees

A working tree may contain valuable in-progress fixes. Do not use a blanket `git stash`, hard reset, checkout, or cleanup to compare against base. Use a separate worktree or inspect narrowly while preserving the current diff.

## Completion report

Report concisely:

- what changed;
- why and which invariant/design it implements;
- selected operating mode and reviewers;
- checks run and their results;
- measurement count/budget when performance evidence was collected;
- progress/design records updated or explicitly deferred;
- files or checks not covered;
- remaining risk, blocker, or decision point;
- commits and branch when applicable.

A green check is not a substitute for explaining the root cause or design fit. A code change with required repository-state records still unsynchronized is not complete unless the deferral is explicit.
