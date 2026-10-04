# Yulang question board primary entrypoint

Read `README.md`, the selected `question.md` and its history, then the original
worktree's `rules/question-board.md`, `rules/design-authority.md` and
`notes/design/2026-10-04-questioner-integrated-answer-handoff.md` §§1–5.
The questioning primary also reads `rules/git-concurrency.md` for integration.
Use exact worktree/branch/source locators. Another worktree cannot see pending
files. Missing context/authority blocks only affected work; do not guess.

## Role selection and file writers

The working/questioning primary writes questions/receipts, maintains bootstrap
and repository records, validates local answers and alone performs Git integration.
Act as answering primary only in a separate user conversation explaining and
answering a selected question; it is not a child-agent role.

The answering primary writes only the selected `answer-draft.md`, preserved draft
revisions and `approved-answer.md`. Repository sources are read-only context;
questions, receipts, compiler, authority records, bootstrap and templates belong
to the questioning primary. Only one answerer writes each selected question.
These primaries may write disjoint owned paths concurrently without worktree-wide
writer/Git ownership transfer. This is a narrow exception to the general
same-worktree primary-writer restriction, not permission for concurrent child
writers. The answerer never stages, commits, pushes, changes branches or mutates
the index. Do not spawn agents while answering.

## Answering primary: approval and local publication

Explain alternatives, save a complete identified/revisioned draft and scope,
and distinguish exact user wording from interpretation. Display the entire saved
draft for explicit approval of that revision. Preferences, discussion, silence
and paraphrases are not approval. Clarify ambiguity only for the affected answer.
Never invent approval quotes, source revisions or thread locators; mark unavailable
locators explicitly.

After approval, publish `approved-answer.md` last as one complete saved artifact,
containing exact approved draft content/revision and actual approval provenance.
Leave all answer files unstaged/uncommitted and Git-visible. Its complete presence
means finalized local publication; the questioning primary discovers and validates
it before committing the matching question/draft/answer. Report the saved path;
no Git or writer handoff is required.

Preserve earlier pending drafts before revision. Never change finalized draft or
answer content; corrections need a new linked question from the questioning
primary and renewed approval. Preserve questions, finalized answers, receipts and
history. Do not rewrite historical committed handoffs.

## Questioning primary: discovery and integration

Read the board at turn start and before dependent actions. Exclude entire
unintegrated question directories, including approved local answers, from ordinary
checkpoints. Validate identities/revisions, exact approved content/provenance,
current premises/source revisions, intended worktree/branch, scope and authority
before staging. Recheck selected-bundle stability, then commit only the matching
question, approved current draft and approved answer under scoped Git checks.
Unapproved archives stay excluded unless explicitly approved as non-authoritative
history in the displayed bundle; other pending questions remain excluded. If
accidentally staged, remove only known paths, preserving files and unrelated state.

Before consumption, verify current files equal committed versions on the intended
branch. Existing committed answers undergo the same validation. A commit never
substitutes for approval. The questioning primary owns receipts and prevents
duplicate consumption. Approval/integration waive no independent review or durable
design gate; record reviewed decisions in governing sources before implementation.

Posting does not pause a goal or suppress independent work on owned paths. No
watcher, service, background polling or automatic pause/wake/resume is added.
A saved answer neither notifies another thread nor resumes a stopped goal.

Direct conversation follows the root Japanese style: no honorific endings, first
person 私, gentle plain speech. Artifacts retain their intended technical register.
