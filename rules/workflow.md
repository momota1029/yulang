# Development workflow

## Establish current context

Before changing the repository, read only the context needed for the task:

- `tasks/current.md` for the current objective and immediate work;
- `notes/design/INDEX.md`, then the relevant authoritative design section;
- `spec/` when the language contract is involved;
- a relevant handoff note under `notes/` when one exists;
- the current daily record under `notes/progress/daily/` when continuity matters.

Do not reread a giant design document indiscriminately when the index or task identifies the governing section. Do not treat `tasks/current.md` as a design authority.

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
- surface: internal, public, or documentation.

Name the intended files, checks, and stop condition. Do not expand a bug fix into unrelated cleanup, rename, formatting, or abstraction work. One coherent change should correspond to one cause or one confirmed gate.

## Order of work

Prefer this order:

1. locate the public entrypoint and owning responsibility;
2. identify the governing design and invariant;
3. establish the smallest coherent scope;
4. change the central type/function or owner first;
5. place helpers behind a visible responsibility boundary;
6. check for new rescans, recomputation, allocation, or hidden coupling;
7. add or update focused tests when behavior changes;
8. run the narrow relevant checks;
9. inspect the diff for scope and responsibility clarity;
10. obtain the required independent review.

For an authoritative multi-gate plan, each gate is normally a coherent slice and commit. Do not combine later gates merely because the current edit is nearby.

## Decision points

A subagent must not ask interactive permission questions. If a necessary decision is absent, it stops the affected work and reports:

- the exact decision;
- why repository evidence does not resolve it;
- available options and consequences;
- work that remains safe and complete.

The primary agent resolves ordinary repository ambiguity and presents only genuine author/user decisions.

## Progress records

Long or multi-step work reports at meaningful milestones: relevant files found, root cause found, before a write, after a coherent slice, after checks, and on a blocker or scope expansion. Avoid line-by-line narration.

`tasks/current.md` is navigation: current objective, governing design/section, active gate, immediate next action, blockers, and known residuals. Completed gates, long commit histories, test-count chronology, and review detail belong under `notes/progress/`.

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
- checks run and their results;
- files or checks not covered;
- remaining risk, blocker, or decision point;
- commits and branch when applicable.

A green check is not a substitute for explaining the root cause or design fit.
