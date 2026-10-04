# Yulang worktree question board

Use for goal-driven Yulang decisions and explicit board requests. Ordinary
conversational clarifications need no entry. Read `AGENTS.md` and the selected
question before answering.

The board is `questions/` in the original active worktree, currently
`/home/momota1029/rust/yulang/questions/`. Use the question's exact absolute path;
another worktree cannot see uncommitted files. This is a local handoff with no
remote transport or automatic delivery.

Authority: [questioner-integrated handoff](../notes/design/2026-10-04-questioner-integrated-answer-handoff.md)
§§1–5. Detailed policy: [question-board rule](../rules/question-board.md).

## Separate answering conversation

Example instruction:

> Open `/home/momota1029/rust/yulang/questions/`, read `AGENTS.md`, and explain
> `<question-directory>/question.md`. Save and display a complete identified
> answer draft for my explicit approval. After approval, save the finalized
> answer locally. Do not stage, commit or push; the questioning primary will
> discover, validate and commit the matching question and answer.

The answerer is this conversation's primary, not a child. It writes only the
selected answer files/history, with one answerer per question. The questioning
primary retains all Git and other repository writes. Both may continue on
disjoint owned paths; no worktree-wide ownership handoff is needed.

## Files and approval

| File in a unique question directory | Sole writer |
| --- | --- |
| `question.md` | questioning primary |
| `answer-draft.md` and preserved draft revisions | answering primary |
| `approved-answer.md` | answering primary |
| `receipt.md` | questioning primary |

Bootstrap/blank templates are infrastructure, not live questions or approval.
All unintegrated question directories stay unstaged/uncommitted and Git-visible,
including approved local answers; ordinary checkpoints exclude them.

Save and display the complete identified draft, distinguish user wording from
interpretation, and obtain explicit approval of that displayed revision. Discussion,
preferences, silence or paraphrases are not approval. Save `approved-answer.md`
last as one complete artifact with exact approved content and actual provenance.
Preserve finalized draft/answer content; corrections need a new linked question
and renewed approval. Archive earlier pending drafts before revising them.
Preserve existing committed handoffs.

## Discovery and commit

The questioning primary reads the board at turn start and before dependent work.
When it finds a finalized local answer, it validates identities/revisions, exact
draft content, approval provenance, current premises/source revisions, scope,
branch/worktree and authority. Recheck bundle stability, then commit the selected
matching question, approved current draft and approved answer together under scoped
Git checks. Unapproved archives stay excluded unless explicitly approved as
non-authoritative history in the displayed bundle. Other pending questions stay
excluded. The answerer performs no Git mutation.

Consume only a fresh valid committed bundle whose current files match committed
versions on the intended branch. A commit never proves approval. Preserve and
reject stale/ambiguous/mismatched answers only for affected work. The questioning
primary writes the receipt and avoids applying a consumed answer again. Record
reviewed user-approved durable decisions in governing sources before implementation.

Posting does not pause a goal; continue independent authorized work. No watcher,
background polling, notification or automatic goal pause/wake/resume exists.
Necessary resumption follows the live runtime contract. Approval/integration waive
no independent review or compiler implementation gate.
