# Development workflow

## Establish context

Read only what the task needs:

- the relevant Authoritative design in `notes/design/` (start from its `INDEX.md`);
- `syntax-reference/` when the surface syntax is involved;
- the code and tests of the responsibility being changed.

Do not reread a giant design document indiscriminately; locate the governing section first and quote the decision used.
Historical material from the 2026-10 proof sprint is in tag `archive/proof-sprint-2026-11-04`. It is a quarry, not authority.

## Work shape

- One request, one bounded piece of work. No resident loops, no self-selected next sprint.
- State the objective, scope, constraints, and stop condition before a non-trivial change.
- Diagnose before editing (see `bug-fixing.md`). Fix at the owning responsibility.
- When a language-semantics or architecture decision is needed, stop and give the user the options with a recommendation. Do not decide it locally.
- Keep unrelated cleanup out of the change.

## Delegation

Delegating to another agent (for example Codex) does not move authority. The delegator gives the objective, scope, constraints, stop condition and required checks, then verifies the result against the actual diff. A delegate's report is a lead, not verification.

## Records

- Design decisions live in `notes/design/` with status (Draft / Authoritative / Superseded), date and scope. Update `notes/design/INDEX.md` when adding one.
- Core calculus and proofs live in Lean and its companion document; their layout is decided when that work starts.
- Do not keep a running task-state file that duplicates Git history. Commit messages state what changed and why.

## Completion report

State what changed, which commands ran with their results, what was not verified, and any remaining decision for the user.
