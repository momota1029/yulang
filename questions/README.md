# Yulang worktree question board

Use this board for user decisions in goal-driven Yulang work and explicit board
requests. Ordinary conversational clarifications need no board entry. Read
`AGENTS.md` and the selected question before answering.

The board is `questions/` in the original active worktree, currently
`/home/momota1029/rust/yulang/questions/`. Use the exact absolute worktree path
recorded in the question: another worktree cannot see its uncommitted files.
This is a local file handoff, without remote transport or automatic delivery.

Authority: `../notes/design/2026-10-04-inrepo-uncommitted-question-board.md` §§1–5.
Detailed policy: `../rules/question-board.md`.

## Separate answering conversation

Example instruction for the user's separate conversation:

> Open `/home/momota1029/rust/yulang/questions/`, read `AGENTS.md`, and explain
> `<question-directory>/question.md`. Display the complete identified answer
> draft for my explicit approval. Establish exclusive worktree writer and Git
> ownership before saving answer files or integrating the approved answer.

The answering agent is that conversation's primary, not a child agent. Transfer
exclusive writer/Git ownership from the working primary before writes, and
return it afterward. Only one primary may be write-capable; serial commands
alone do not establish ownership. During the handoff, the original goal may
continue independent read-only work. Without ownership, explanation and drafting
can continue in chat while file/Git publication waits.

## Files and approval

| File in a unique question directory | Sole writer |
| --- | --- |
| `question.md` | working primary |
| `answer-draft.md` | answering primary |
| `approved-answer.md` | answering primary |
| `receipt.md` (after validation) | working primary |

The tracked bootstrap and blank forms in `templates/` are not live questions,
answers, approvals or authority. Maintain them only as the working primary.

Actual pending question directories, including drafts and unapproved history,
remain unstaged and uncommitted. They are visible with
`git status --short --untracked-files=all -- questions`; do not ignore them.
Every ordinary checkpoint excludes these entire pending directories.

Save and display the complete identified draft, distinguish user quotes from
interpretation, then obtain explicit approval of that exact displayed revision.
Discussion, preferences, silence and assistant paraphrases are not approval.
After approval, save exact approved content and actual approval provenance.
The answering primary commits the selected question, approved current draft and
approved answer together under the scoped Git checks in `rules/git-concurrency.md`.
Earlier unapproved draft archives remain excluded unless the user explicitly
approves including those files as non-authoritative history in the displayed
bundle. Such optional history is not required for ordinary answering. Other
pending questions remain excluded. Child agents have no Git authority.

The working primary consumes only committed matching exact question/draft/answer
on the intended branch whose current files match those committed versions and
whose premises, revisions, provenance, scope and authority remain valid. A commit
never proves approval. Reject changed, stale, ambiguous or mismatched handoffs
only for affected work. Write a receipt after validation; it may enter the next
coherent commit. Do not consume an unchanged accepted answer twice.

Preserve questions, approved content, receipts and history. Archive earlier
pending draft revisions before revising them. Corrections to approved content
use a new linked question and renewed approval; never overwrite old approval.

Posting never pauses a goal. Unanswered questions block only dependent actions;
continue independent authorized work, with read-only work during another primary's
writer handoff. Read the board at turn start and before dependent actions. Do not
repeatedly repost or budget-poll. No watcher, helper, service or automatic goal
pause/wake/resume exists; resumption follows the live runtime contract.
Approval and a commit do not waive independent review or durable-design gates.
Record reviewed, approved durable decisions in governing repository sources
before implementation.
