# Questioner-integrated local answer handoff

Status: Authoritative
Scope: Yulang question-board file writers, local answer discovery and questioner-owned Git integration
Approved-by: user (current explicit workflow change request)
Approved-at: 2026-10-04
Drafted-by: primary
Reviewed-by: spec_auditor (`question_writer_scope`, isolated read-only pre-write review; no findings)
Supersedes: 2026-10-04-inrepo-uncommitted-question-board.md §§3–4 for integration ownership, discovery and writer handoff; all unchanged approval/revision/authority safeguards retained

## 1. Explicit user decision

The user requested:

> OK．ルールを変えましょう．質問者は質問をコミットしない．回答者は回答をコミットしない．質問者が回答を発見したらどちらもコミットする．これでどうでしょう．所有権の問題は発生しません．

The working/questioning primary publishes the question locally without committing
it. The separate answering primary saves an explicitly approved answer locally
without any Git mutation. The questioning primary discovers, validates and
commits the matching question, approved current draft and finalized answer.
The same requested workflow needs no repeated approval prompt.

## 2. File writers and Git authority

Keep `questions/` in the original worktree and the four existing interface names.
The questioning primary alone writes questions and receipts and retains all Git,
compiler/source, infrastructure and authority-record responsibilities. The
answering primary writes only the selected `answer-draft.md`, preserved draft
revisions and `approved-answer.md`; repository sources are read-only context.
Only one answering primary may write a selected question's answer files.

These two primaries may work concurrently in the same worktree on their disjoint
owned paths. No worktree-wide writer/Git ownership transfer is required. This
is a narrow exception to the general same-worktree primary-writer restriction;
it grants no Git rights to the answerer and no concurrent write-capable child
agents. Source work can continue while an answer is prepared; the questioning
primary revalidates its premises before integration. A concrete overlapping
path or index conflict blocks only the affected action.

## 3. Complete approved local publication

Preserve explicit approval of the complete saved and displayed identified draft.
User wording and the answerer's interpretation remain distinguished. A preference,
discussion, silence or commit never substitutes for approval. Draft edits require
new revisions, preserved history, a complete display and renewed approval.

Save the full approved draft before publishing `approved-answer.md`. Publish that
file as one complete saved artifact, last, containing the exact approved content,
identities/revisions, actual approval provenance and scope. Its completed presence
marks a finalized local answer, not a committed or already consumed decision.
Once finalized, neither that draft nor answer is edited; corrections use a new
linked question and renewed approval. Preserve historical questions and answers.
The answerer never stages, commits, pushes, changes branches or mutates the index.

All unintegrated question directories, including approved local answers, stay
unstaged/uncommitted and Git-visible. Ordinary checkpoints exclude them. Earlier
unapproved archives remain excluded from integration unless explicitly approved
as non-authoritative history in the displayed bundle. Other pending questions
are always excluded.

## 4. Questioner discovery, validation and integration

At turn start and before dependent actions, the questioning primary reads the
board. Discover an uncommitted finalized answer through those ordinary reads;
no watcher, background poller, notification or automatic goal lifecycle action
is introduced.

Before staging, validate question and draft identities/revisions, exact approved
content, explicit approval provenance, current premises/source revisions,
branch/worktree, authorized scope and governing authority. A partial, stale,
conflicting or ambiguous answer blocks only its affected scope; preserve it and
record a rejection receipt and user-facing explanation. Do not change finalized
answer content to repair a mismatch.

Recheck that the complete selected bundle is unchanged between validation and
staging. Integrate only the explicit matching question, approved current draft
and approved answer under normal staged-scope/upstream/outbound-range checks.
The questioner owns this commit and the normal coherent push. Before consumption,
verify the current files equal their committed versions on the intended branch.
An integration commit is not approval evidence. Write the working-owned receipt
with validation, commit locator, outcome and affected scope; it can enter the
next coherent commit. An unchanged consumed answer is never applied twice.

Existing committed handoffs remain eligible under the same identity, exactness,
provenance, scope and freshness checks. Do not rewrite them to migrate the
workflow. Record reviewed, user-approved durable decisions in governing sources
before implementation; answer discovery/integration waives no design or review
gate. No compiler implementation is authorized by this workflow change.

## 5. Delivery and verification budget

Update active rules, root/nested entrypoints, blank templates and workflow/index
navigation. Preserve earlier design/progress records as history. The primary
owns task/progress synchronization and scoped Git integration.

Mode M2: one pre-write spec scope reviewer and one fresh closure spec reviewer;
no architect is needed for the settled user decision. Converge with no accepted
blocking/major findings. Use focused file/reference, blank-template, scope and
diff checks; zero compiler tests/builds or performance samples/processes.
