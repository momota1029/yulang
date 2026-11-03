# Git safety

- Stage explicit paths. Inspect the branch, `git status`, and the staged diff before every commit.
- One coherent cause per commit. Separate behavior from formatting-only drift, bug fixes from unrelated cleanup, and mechanical relocation from semantic change.
- Do not push, force-push, rewrite history, or delete branches unless the user asked.
- Do not use blanket `git clean`, `git reset --hard`, or `git stash` on a tree with work you did not make. Use a separate worktree for baseline comparison.
- When two agents might write at once, give each its own worktree and distinct paths. Concurrent writers on one tree are not allowed.
- Archived history is read through its tag (`archive/proof-sprint-2026-11-04`); do not move or delete that tag.
