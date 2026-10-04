# Yulang question board

Status: Authoritative
Scope: Yulang-only file handoff between a working primary and a separate answering primary
Approved-by: user
Approved-at: 2026-10-04
Drafted-by: primary with architect advisory
Reviewed-by: spec_auditor (`question_board_review`, isolated read-only proposal review)
Supersedes: none

## 1. Approval and boundary

The user selected Yulang-only operation and an explicit approval step after
the answering primary organizes an answer draft. The primary presented the
external location, four-file handoff, revision validation, unaffected-work
continuation, and retained design/implementation gates. The user's response
`良さそう` approves that presented workflow and creation of its folder and rules.
The earlier independent proposal review found no blocking or major issue.
This approval does not authorize compiler implementation or change the active
inference objective.

## 2. Location and ownership

The shared board is `/home/momota1029/.local/share/yulang/question-board/`
(`~/.local/share/yulang/question-board/` for this user's account), outside the
compiler worktree. Other worktrees of this Yulang repository use the same
absolute location. It is a local handoff, not a remote transport or Git branch
copy. Repository policy is maintained in `rules/question-board.md`; local
instructions and templates make the answering entrypoint self-contained.

Each unique question directory contains:

| File | Owner | Meaning |
| --- | --- | --- |
| `question.md` | working primary | Question and its revision, task/thread locator when available, repository/branch and relevant source revision, background, options and consequences, and blocked scope |
| `answer-draft.md` | answering primary | Displayed answer draft revision, question revision, user wording distinguished from interpretation, and proposed decision and scope |
| `approved-answer.md` | answering primary | Exact approved draft content/revision, question revision, explicit approval provenance, and authorized scope |
| `receipt.md` | working primary | Validation and acceptance/application, or rejection and reason |

The answering primary operates from the board directory and writes only its
answer files. It does not edit the compiler worktree or perform repository Git
integration. The working primary retains authority resolution and repository
record synchronization. Publication is serialized and only complete saved
files are published; files have one owner and are not jointly edited.

## 3. Answer and approval lifecycle

The answering primary explains the question and alternatives in plain language,
then displays the complete answer draft for explicit user approval. Discussion,
preferences, silence, and an assistant's paraphrase do not themselves finalize
an answer. Approval must unambiguously refer to the displayed draft revision;
otherwise only the affected answer waits for clarification.

The finalized answer preserves the exact approved content and approval
provenance. An edit after approval requires a new draft revision and renewed
approval. Published question revisions and finalized answers are preserved;
changed question premises require a new revision and cannot inherit old
approval silently. Revision history can use new question directories linked to
their predecessors; filenames remain the four-file interface above.

The working primary reads the board at each turn start and before dependent
actions. It validates question/draft identity, current premises, provenance,
scope and governing authority, then writes a receipt. Unchanged, already
consumed approvals are not applied again. An outdated, conflicting, or ambiguous
answer leaves the affected work waiting and receives an explanatory receipt.

## 4. Goal and authority boundaries

An unanswered question blocks only dependent work. Continue independent
authorized work; do not guess the answer, repeatedly repost the same question,
or poll solely to consume a goal budget.

A saved answer neither notifies another thread automatically nor wakes or
resumes a stopped goal. Goal lifecycle actions obey the live tool contract;
necessary resumption is performed in the original thread under user/system
control. No watcher or automatic resumption service is introduced.

Approval of an answer does not waive independent design review or other
implementation gates. Before implementing a new durable decision, the working
primary records its reviewed, user-approved scope in the governing repository
records under `rules/design-authority.md`. The board is a handoff with provenance,
not a substitute for repository authority.

## 5. Delivery and verification

Deliver repository routing, the detailed rule, a local board entrypoint and
blank templates. Do not create a fictitious pending question or approval.
Use a focused independent conformance review of approval, revision, ownership
and lifecycle boundaries, plus file/reference inspection. Compiler builds,
tests and performance measurements are outside this policy-only change.
On an invalid answer, preserve history, reject only the affected handoff, and
return that decision to the user; do not roll back unrelated work.
