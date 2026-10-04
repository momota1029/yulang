# Yulang question board

Authority: `notes/design/2026-10-04-yulang-question-board.md` (Authoritative).
This rule implements its Yulang-only, explicitly approved file handoff.
Use it for user decisions in goal-driven Yulang work and explicit board
requests; ordinary conversational clarifications need not create board questions.

## Location and ownership

Use `/home/momota1029/.local/share/yulang/question-board/` across this
repository's worktrees. This local directory is outside the compiler worktree;
it is not remote transport or a Git branch copy. Its `AGENTS.md`, `README.md`
and blank `templates/` make a separate answering thread self-contained.
Bootstrap maintenance belongs to the working primary. Templates are not
pending questions, decisions, approvals, or authority.

Each unique question directory uses this interface:

| File | Sole writer | Purpose |
| --- | --- | --- |
| `question.md` | working primary | Question revision, premises, options, consequences and blocked scope |
| `answer-draft.md` | answering primary | Complete displayed draft and its revision |
| `approved-answer.md` | answering primary | Exact approved content/revision and approval provenance |
| `receipt.md` | working primary | Validation, acceptance/application, duplicate consumption or rejection |

Do not jointly edit files or publish concurrently. Serialize publication;
save the complete content before presenting a file as published. The answering
primary operates from the board and writes only its answer files. It does not
edit the compiler worktree, perform Git integration, or spawn agents. It may
read the relevant repository sources to understand the question. The working
primary retains authority resolution and repository record synchronization.
Do not add a watcher, service, polling tool or automatic resumption mechanism.

## Working primary: publish and consume

1. At each turn start, read the board for applicable questions, finalized
   answers and receipts. Read again before an action dependent on an answer.
2. For an unresolved decision, create a unique question directory and complete
   `question.md`: question identity/revision, repository and branch, relevant
   source revisions, task/thread locator when available, premises, alternatives
   with consequences, requested decision and precisely blocked scope. State
   explicitly when a thread locator is unavailable. Publish only saved complete
   content; do not create a fictitious pending question.
3. Keep dependent work waiting and continue independent authorized work. Do not
   guess, repeatedly repost the same question, or poll solely to consume a goal
   budget. Reading at the required boundaries is not a background polling loop.
4. On a finalized answer, validate question identity/revision and draft
   identity/revision, exact approved content, explicit approval provenance,
   current premises and source revisions, authorized scope and governing
   authority. A preference, discussion, silence or assistant paraphrase is not
   approval. Approval must unambiguously identify the displayed draft revision.
5. Write `receipt.md` with the identities/revisions, validation evidence,
   outcome, reason and affected scope. Accept and apply only a fresh, valid
   handoff within its authority. Record where the accepted decision was applied
   or which repository gates still precede implementation. An unchanged answer
   already recorded as consumed is not applied again; retain that receipt.
6. For an outdated, conflicting or ambiguous answer, preserve history and write
   an explanatory rejection receipt. Leave only affected work waiting and return
   the rejection to the user. Do not roll back unrelated work.

## Answering primary: draft and approval

1. Read the board entrypoint and selected `question.md`. Check its revision,
   premises, relevant sources and any existing answer history before writing.
2. Explain the question and alternatives in plain language. Save a complete
   `answer-draft.md` containing question/draft identities and revisions, the
   proposed decision and its exact scope, and user wording distinguished from
   the answering primary's interpretation.
3. Display the complete saved draft to the user, including its revision. Obtain
   explicit approval unambiguously referring to that displayed revision. If
   approval is ambiguous, only the affected answer waits for clarification.
4. After approval, save `approved-answer.md` with the exact approved draft
   content/revision, question revision, explicit approval quote and provenance,
   and authorized scope. Do not invent quotes, source revisions or locators.
   Finalize only complete saved content, with serialized publication.
5. Never modify approved content. An edit needs a new draft revision, a complete
   display and renewed approval. Preserve earlier draft revisions before
   replacing the current draft, using archived revision files or a new linked
   question directory. Preserve published questions and finalized answers;
   changed premises use a new linked question directory/revision and cannot
   silently inherit approval. The four interface filenames remain unchanged.

## Lifecycle and durable authority

A saved answer does not notify another thread, wake a stopped goal or resume
one. Necessary resumption occurs in the original thread under user/system
control and the live goal-tool contract. Do not imply automatic delivery.

An approved answer is a handoff with provenance. It does not waive independent
design review, implementation review or other gates. Before implementing a new
durable decision, the working primary records the reviewed, user-approved scope
in the governing repository records under `rules/design-authority.md`. Existing
Authoritative scope remains binding; unresolved authority stops only affected
work. Bootstrap delivery uses focused conformance and file/reference inspection,
without compiler tests, builds or performance measurements.
