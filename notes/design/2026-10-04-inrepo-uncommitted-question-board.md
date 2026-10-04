# Repository question board with pending questions outside commits

Status: Authoritative
Scope: Yulang branch-local question storage, approval-before-commit handoff and serialized primary ownership
Approved-by: user (current explicit change request)
Approved-at: 2026-10-04
Drafted-by: primary with `inrepo_board_design_check` architect advisory
Reviewed-by: spec_auditor (`inrepo_board_scope_review`, isolated read-only scope review)
Supersedes: 2026-10-04-yulang-question-board.md sections 2–5 for location, answer integration and delivery; approval/revision/authority safeguards retained

## 1. Current user decision

The user explicitly requested: `Yulangの中で質問スレッドを作り，それを**コミットしない**`.
They then find the uncommitted question, open a separate conversation to explain
and answer it, and commit afterward (`そしたらコミットする`). The earlier explicit
choice to display an answer draft and obtain approval before finalization remains.
This request authorizes the location/integration change; no further approval of
those same choices is needed. Independent scope review found no blocking, major
or minor finding before implementation.

## 2. Repository location and visibility

Use `questions/` in the Yulang worktree containing the active work. Track its
`README.md`, nested `AGENTS.md` and four blank forms under `templates/`.
Create one unique directory per actual question with `question.md`,
`answer-draft.md`, `approved-answer.md` and later `receipt.md`.

The answering conversation reads the exact worktree path recorded in the
question; another worktree does not inherit uncommitted files. No external
shared directory, remote transport, Git ignore rule or watcher is introduced.
Retire the former external entrypoint with a pointer to the repository board,
preserving any local history rather than deleting it.

## 3. Pending and committed handoff

Unanswered questions and unapproved drafts remain unstaged and uncommitted,
visible in `git status`. All ordinary checkpoint commits exclude pending
question directories, even while other authorized work is committed/pushed.
If accidentally staged, remove only the known pending paths from the index,
preserving their files and all unrelated state. Never blanket-stash/reset/clean.

The answering primary explains the question, saves and displays a complete
identified draft, and obtains explicit approval of that exact revision.
Only then finalize an answer with exact approved content and actual approval
provenance, and commit the selected question, approved draft/history and
approved answer together. Unapproved drafts or other pending questions are
excluded. The answering primary owns this scoped Git integration under the
usual branch/upstream/outbound-range checks and coherent push policy.

The working primary consumes only a finalized answer whose exact content and
matching question/draft are committed on the intended branch, whose current
files match those committed versions, and whose premises/scope remain valid.
Commit existence never substitutes for explicit approval. Reject stale,
ambiguous, mismatched or changed content only for affected work. Record a
receipt after validation; it can enter the next coherent commit. Do not reapply
an already consumed unchanged answer. Preserve published questions, approved
content, receipts and history; corrections use a new linked question/revision
and renewed approval rather than rewriting prior approval.

## 4. Primary ownership and goal boundary

The working primary owns question/receipt files; the answering primary owns
answer files and the approved-answer commit. Both are primary agents in their
own conversations; this grants no Git authority to subagents.

Before the answering primary writes or integrates, explicitly hand off worktree
writer and Git ownership from the working primary. Only one primary has that
ownership at a time. The working goal may continue independent read-only work
during the handoff. Return ownership afterward. Serializing individual commands
alone does not permit two concurrent write-capable agents. If ownership cannot
be established, continue explanation/drafting in chat, and wait only on file/Git
publication; do not pause the goal merely because a question was posted.

At turn start and before dependent work, the working primary reads the board
and validates committed approvals. Unanswered questions stop dependent actions
only; continue other authorized work and exclude pending entries from commits.
Do not repeatedly repost or budget-poll. This workflow adds no automatic goal
pause, wake or resume mechanism and makes no guarantee of automatic resumption
if the runtime actually stops. Lifecycle control follows the live tool contract.

## 5. Authority and delivery

Board approval and its commit do not waive independent review or durable-design
gates. Record reviewed, approved decisions in their governing repository sources
before implementing new durable choices. The inference objective and compiler
implementation authorization are unaffected.

Deliver the successor, rule/routing switch, tracked bootstrap/templates and
progress/task navigation. Preserve concurrent edits. Verify with isolated
conformance review plus focused file/reference, index and diff inspection;
no compiler tests/builds or performance measurements. Mode M2: one architect
advisory, at most two spec auditors per round covering pre-write scope and final delivery;
converge with no accepted blocking/major findings. Primary owns bookkeeping/Git.
