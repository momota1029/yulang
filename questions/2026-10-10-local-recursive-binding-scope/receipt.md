# Receipt: local recursive binding scope

Question ID: `local-recursive-binding-scope`
Question revision: `q1`
Draft ID/revision: `local-recursive-binding-scope-answer/a1`
Approved answer locator: `approved-answer.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Current relevant source revision(s): question baseline `5daa64d6a`; current validation `8de33dc73`; Oracle pin `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Task/thread locator: unavailable; no stable conversation identifier is exposed
Governing source/section: `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` §3; `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Selected operation”; `notes/progress/2026-10-10-generic-local-source-hir.md`, “Implementation”

## Local answer discovery

The complete q1/a1 bundle was present in the original question worktree. The
approved file records the user's explicit `OK` after both complete answer
drafts were shown, and selects option 1 for this question.

## Pre-integration validation and bundle stability

- Question, draft and approved answer identify the same question q1 and draft
  `local-recursive-binding-scope-answer/a1`, intended worktree and branch.
- The exact approved content matches `answer-draft.md` after removing the
  Markdown section-separator blank line; no substantive byte differs.
- The approval quote is explicit. The selected scope is one local function
  visible during its own initializer, one open monomorphic live root shared by
  recursive occurrences, and retention of that root/boundary for later
  capture/freshening. Sibling visibility stays sequential; local mutual groups,
  polymorphic recursion, general self-initialization and new annotation rules
  are excluded.
- The question baseline is an ancestor of current HEAD. Current source lowering
  still makes local bindings sequential and no local self-recursive regression
  exists. The Authoritative nested-block addendum §3 explicitly left recursive
  local definitions undecided, so the user selection supersedes only that
  boundary after a narrow reviewed addendum records it.
- All three current files were unchanged from validation through commit.

## Approved handoff commit

Integrated on the intended branch in commit `8de33dc73` (`questions: select
local self-recursive binding scope`) and pushed to
`origin/research/simple-sub-intrusion`. Current files match the committed
versions.

## Validation and outcome

Accepted and consumed once: a single local function may refer to itself while
its initializer is inferred, and those occurrences constrain the same open
monomorphic root. Once initializer constraints exist, the live root and
boundary remain available for later capture/freshening. Neighboring bindings
remain sequential. Mutual local recursion and polymorphic recursion are not
selected.

This consumes only the scope decision. It does not claim HIR identity formation,
solver scheduling, live-scheme transition, rollback, source conformance,
soundness/principality, production migration or F5 replacement. The reviewed
authority addendum records the decision; implementation still requires the
focused HIR/solver lifecycle and rollback/fresh-use evidence listed there.

Application/consumption record: [`notes/design/2026-10-10-local-self-recursive-binding.md`](../../notes/design/2026-10-10-local-self-recursive-binding.md)
and `tasks/current.md`.
Repository records/gates: the nested-block addendum remains authoritative for
its existing scope; the new Authoritative addendum supersedes only its §3
recursive-local-declarations boundary for the selected single-binding case.
Affected work waiting: source/HIR/solver support for a single local
self-recursive function, pending the implementation and focused verification
gate in the authoritative design. Module-level recursion and independent work
continue.
History retained: q1/a1 and this receipt in this directory.
User-facing rejection returned: not applicable.
