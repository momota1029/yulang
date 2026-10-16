# Yulang question board

Authority: `notes/design/2026-10-04-questioner-integrated-answer-handoff.md`
§§1–5, plus the [2026-10-16 operational addendum](../notes/design/2026-10-16-resident-loop-operations-addendum.md) on bundle contents and receipt timing. Earlier approval/revision/authority safeguards remain binding. Use for goal-driven Yulang decisions and explicit board requests;
ordinary conversational clarifications need not create questions.

## Location, file writers and Git authority

Use `questions/` in the exact active Yulang worktree. Track bootstrap `README.md`,
`AGENTS.md` and four blank `templates/` as infrastructure. All unintegrated
question directories, including approved local answers, remain unstaged and
uncommitted, visible with `git status --short --untracked-files=all -- questions`.
Do not Git-ignore the board. Another worktree does not inherit these files;
the answering conversation opens the question's original absolute worktree.
The retired external board is a historical pointer, not remote transport.

| File | Sole writer | Purpose |
| --- | --- | --- |
| `question.md` | working/questioning primary | Revision, premises, alternatives and blocked scope |
| `answer-draft.md` and draft archives | answering primary | Complete displayed draft and history |
| `approved-answer.md` | answering primary | Exact approved content/revision and provenance |
| `receipt.md` | working/questioning primary | Validation, integration, consumption or rejection |

The questioning primary retains all Git, repository source, bootstrap and
record responsibilities. The answering primary is a separate user conversation's
primary, not a child; source context is read-only, and its writes are restricted
to the selected answer files/history. Only one answerer writes each question.
It never stages, commits, pushes, changes branches or mutates the index.
No worktree-wide writer/Git ownership handoff is needed. The two primaries may
work concurrently on their disjoint owned paths; this narrow exception grants
no Git rights to children or concurrent write-capable child-agent permission.
A concrete overlapping-path/index conflict blocks only the affected action.

Ordinary checkpoints exclude entire unintegrated question directories, even
approved local answers. Once the questioner validates a selected explicitly
approved answer, stage and commit **the entire curated question directory** in
one commit: question, current approved draft, final answer, earlier attempt/revision
history as non-authoritative provenance, and the validation receipt. Protect
all other pending questions and verify the file inventory for secrets and
other-worker output. A commit never proves approval. If pending
paths were accidentally staged, remove only known paths from the index, preserving
files and unrelated state; never blanket-stash/reset/clean.

## Questioning primary: publish, discover, integrate and consume

1. At turn start and before dependent actions, read applicable questions,
   finalized local answers and receipts. Do not background-poll for answers.
2. Save a complete unique `question.md` for a real unresolved decision: identity,
   revision, worktree/branch, source revisions, task/thread locator (explicitly
   unavailable when absent), premises, alternatives/consequences, requested
   decision and exact blocked scope. Publish it without committing.
3. Keep only dependent work waiting. Continue independent authorized work on
   owned paths while the answerer prepares the answer. Do not guess, repeatedly
   repost questions or poll to consume a goal budget.
4. Discover the complete finalized `approved-answer.md` locally. Before staging,
   validate question/draft identities and revisions, exact approved draft content,
   explicit approval quote/provenance, current premises/source revisions, intended
   worktree/branch, authorized scope and governing authority. Partial files,
   preferences, discussion, silence and paraphrases are not approval.
5. Before integration, prepare the questioner's `receipt.md` with exact approval
   evidence, selected revision, file inventory/validation and an integration
   locator resolved from the containing bundle commit. Freeze/recheck the
   selected directory; stage **that entire curated directory**, including all
   intentional intermediate and failed-attempt files as non-authoritative history.
   Commit in **one coherent bundle**. Exclude unrelated or pending questions.
   Inspect staged scope and the intended outbound range before safe push.
6. Consume only after committed/current bytes match on the intended branch,
   approved content still validates, and the actual bundle SHA can be recovered
   from the selected directory's Git history.
7. Keep the validation receipt **in that bundle commit**; a file cannot contain
   its own immutable commit SHA. Record any subsequent integration/consumption
   metadata in task/progress records outside the finalized question directory.
   Retain receipts and never reapply an unchanged consumed answer.
8. Preserve partial, outdated, conflicting or ambiguous answers, write an
   explanatory rejection receipt and return the rejection to the user. Leave
   only affected work waiting; do not roll back unrelated work or edit finalized
   answer content.

## Answering primary: draft, approval and local publication

1. Read the board entrypoint, selected question revision/premises, sources and
   answer history in the original worktree. No writer/Git handoff is needed.
2. Explain alternatives plainly. Save a complete identified/revisioned
   `answer-draft.md` with exact proposed scope and user wording distinguished
   from interpretation. Write only the selected answer paths/history.
3. Display the complete saved draft and revision. Obtain explicit approval
   unambiguously referring to it. Ambiguity blocks only the affected answer.
4. After approval, save `approved-answer.md` last as one complete artifact with
   exact approved draft content/revision, question revision, actual approval
   quote/provenance and scope. Never invent quotes/revisions/locators. Completed
   presence marks finalized local publication, not integration or consumption.
   Leave the directory unstaged/uncommitted and report its path; the questioning
   primary discovers, validates and commits it.
5. Never modify finalized draft/answer content. Corrections need a new linked
   question from the questioning primary and renewed approval. Preserve earlier
   pending drafts before replacement; use a new revision, complete display and
   renewed approval. Preserve questions, answers and history; changed premises
   never inherit approval silently. Keep the four interface names. Do not rewrite
   earlier committed handoffs.

## Lifecycle and durable authority

Posting does not pause a goal or suppress independent authorized work. A saved
answer does not notify another thread or wake/resume a stopped goal. No watcher,
service, background polling or automatic lifecycle action is introduced; required
resumption follows user/system control and the live goal-tool contract.

An approved answer is a handoff with provenance. Discovery and integration waive
no independent design/implementation review. Before implementation, record the
reviewed user-approved durable scope in governing sources under
`rules/design-authority.md`. Existing Authoritative scope remains binding;
unresolved authority stops only affected work. Policy/bootstrap delivery uses
focused file/reference/conformance checks, without compiler tests/builds or
performance measurements. The inference objective and its gates are unchanged.
