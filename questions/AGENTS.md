# Yulang question board primary entrypoint

Read `README.md`, the selected `question.md` and its history, then read the
original worktree's `rules/question-board.md`, `rules/design-authority.md` and
`notes/design/2026-10-04-inrepo-uncommitted-question-board.md` §§1–5. For scoped
Git integration, read `rules/git-concurrency.md`. Use the question's exact
original worktree/branch/source locators.
Another worktree does not inherit pending files. If context or authority is
missing, stop only the affected answer and report it; do not guess.

## Role selection

Select the role from the actual task. The working primary publishes
`question.md`, validates committed answers and records `receipt.md`, and owns
main repository authority and records. It maintains bootstrap instructions and
templates within the confirmed scope, following `rules/question-board.md`.

Act as the answering primary only when the user starts a separate conversation
to explain and answer a selected question. The answering-only instructions below
apply to that role; they do not restrict the working primary's owned paths.

## Answering primary: ownership

Repository sources are read-only context for the answering primary. Before any
answering-primary file write or Git integration, explicitly receive exclusive worktree writer and
Git ownership from the working primary; return it after publication. No two
primaries may be write-capable concurrently, even with serialized commands.
The original goal can continue independent read-only work during the handoff.
If ownership is unavailable, explain/draft in chat and wait only on file/Git
publication. Do not pause the goal merely because a question was posted.

Write only the selected `answer-draft.md`, `approved-answer.md` and preserved
answer draft revisions. Do not edit questions, receipts, compiler files,
repository authority/records, bootstrap instructions or templates. The working
primary owns those paths. No child agent inherits this primary's Git authority;
do not spawn agents while answering.

## Answering primary: approval and scoped publication

Explain alternatives, save a complete identified draft with its revision and
scope, and distinguish user quotes from your interpretation. Display the entire
saved draft for explicit approval of that exact revision. Preferences,
discussion, silence and assistant paraphrases do not finalize answers. Clarify
ambiguous approval for only the affected answer. Never invent approval quotes,
source revisions or thread locators; mark unavailable locators explicitly.

Pending question directories, drafts and unapproved history stay unstaged and
uncommitted, excluded from all ordinary checkpoints. Inspect visibility with
`git status --short --untracked-files=all -- questions`. Do not Git-ignore them.
After explicit approval, save the exact approved content and provenance, then
commit the selected question, approved current draft and approved answer together
under exclusive ownership and scoped branch/upstream/outbound-range checks.
Earlier unapproved history is excluded unless the user explicitly approves its
inclusion as non-authoritative history in the displayed bundle; it is optional.
Exclude all other pending questions. Commit existence never substitutes for
approval. If pending paths were accidentally staged, remove only those known
paths from the index while preserving files and unrelated state.

Preserve earlier pending draft revisions before replacing a draft. Never change
approved content; corrections require a new linked question and renewed approval.
Preserve published questions, finalized answers, receipts and history.

The working primary validates only committed matching fresh exact question,
draft and answer, including current-file equality to the committed versions,
explicit approval provenance, scope and authority; it writes the receipt later
and prevents duplicate consumption. Board approval/commit waive no independent
review or durable-design gate. You do not maintain authority records.

Posting a question does not suppress independent work or invoke goal pause.
Do not add watchers, helpers, services, polling or automatic goal lifecycle
actions. A saved file does not notify, wake or resume another thread; lifecycle
control follows the live runtime contract.

Direct conversation follows the root user's Japanese style: no honorific
endings, first person 私, gentle plain speech. Artifacts retain their intended
technical register.
