# Git and concurrency safety

## Integration ownership

The primary agent owns staging, commits, branch updates, PRs, and pushes. Subagents report changed paths and checks but do not stage, commit, push, rewrite history, or delete branches.

Stage explicit paths. Do not use `git add -A` in a shared or potentially dirty working tree. Before every commit, inspect the branch, `git status`, staged diff, and whether unrelated concurrent work is present.

## Coherent commits

Prefer one commit per confirmed design gate or coherent cause. Separate:

- behavior from formatting-only drift;
- a bug fix from unrelated cleanup;
- mechanical relocation from semantic change;
- policy extraction from the atomic active-policy switch.

A commit is a reviewable and bisectable checkpoint, not merely a progress timestamp.

## Parallel work

Independent read-only review may run in parallel and reports stay isolated until all reviewers finish.

Do not run two write-capable agents in the same working tree. Use a distinct git worktree and branch for each concurrent writer. Do not use one shared index from several sessions.

## Branch safety

The Codex-only policy on the `yulang3` branch does not authorize changes to frozen `main`. Work on the branch named by the task. Routine pushes of coherent commits to the current working branch are allowed when they preserve the intended remote synchronization; never force-push, rewrite history, or retarget another branch without explicit user instruction.

When upstream moved, re-evaluate scope before integration. Do not force a ref merely to preserve a local plan.

## Generated and temporary files

Do not commit build output, logs, scratch files, tool state, or unrelated formatting drift. Respect `.gitignore`, but do not use ignore rules to hide a source file that should be reviewed.
