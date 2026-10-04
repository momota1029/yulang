# Questioner-integrated answer handoff delivery

Date: 2026-10-04
Branch: research/simple-sub-intrusion
Authority: [explicit user-requested successor](../design/2026-10-04-questioner-integrated-answer-handoff.md) §§1–5

## Scope and decision

The user requested that neither the questioner at initial question publication nor
the answerer at answer publication commits the pending files. The questioner
discovers the finalized local answer, validates it, then commits the matching
question, approved current draft and approved answer. Explicit approval and exact
content/provenance remain required. No repeated approval of this requested workflow
is needed.

The questioner retains all Git/source/infrastructure/receipt authority. The
answerer may write only the selected answer files/history, with one answerer per
question and no Git mutation. Disjoint primary-owned paths need no worktree-wide
ownership transfer; child-writer restrictions remain. A finalized answer is saved
last as one complete artifact and immutable afterward. Validate before integration,
recheck bundle stability, and check committed-file equality before consumption.
All unintegrated directories, including approved answers, stay excluded from
ordinary checkpoints. Existing committed approvals/history remain intact.

## Delivery and records

Updated `rules/question-board.md`, root and nested AGENTS, board README and all
four blank templates, workflow/Git routing and rule/design navigation. Added the
explicitly scoped Authoritative successor; predecessor designs/progress are kept
as historical records. Updated only the workflow navigation paragraph in
`tasks/current.md`, preserving a concurrent unrelated inference-record edit and
excluding that edit from this policy commit.

The existing function-bound q1/r1 answer from commit `b64a506f6` is not rewritten.
Its receipt and any inference authority/application records belong to the original
working primary and are outside this policy maintenance slice. No compiler source,
question/answer history, watcher, service or runtime lifecycle behavior is changed.

## Review and verification budget

Mode M2; settled explicit decision, no architect. Budget: one pre-write scope
spec review and one fresh closure spec review, converging with no accepted
blocking/major findings. Primary owns implementation/records/Git. Verification:
focused file/reference/template/scope/diff checks; zero compiler tests/builds and
zero performance samples/processes.

Pre-write isolated `spec_auditor` (`question_writer_scope`) found no findings and
confirmed implementation fits the explicit authorization. Its named delivery
surfaces and retained safeguards are reflected above.

Fresh isolated closure `spec_auditor` (`question_writer_closure`) inspected the
scoped policy/entrypoint/template diff, successor/progress and top task navigation,
including the direct orchestration parallelism route, and found no blocking,
major or minor findings. No findings required repairs. All required policy/task/
design/progress records are synchronized; nothing in this maintenance slice is
deferred.

Focused checks completed:

- Inline Python file/link/template/active-authority inspection passed for sixteen
  scoped files; local Markdown targets exist, templates remain blank and
  non-authoritative, and active entrypoints use the successor.
- `git diff --check` for changed policy/entrypoint/template/index/task paths passed.
- Existing function-bound question, draft and approved-answer tracked files have
  no content diff; the live receipt is excluded from this slice.
- Final explicit staged-path inspection includes only policy infrastructure,
  successor/delivery records and the workflow navigation hunk of `tasks/current.md`;
  unrelated inference-task/progress hunks remain unstaged.

No compiler tests/builds or performance measurements were run. Live concurrent
sessions and discovery/integration execution remain unverified by these checks.

## Remaining limits

Files communicate locally; publication does not notify another thread or resume a
stopped goal. Discovery occurs at the existing read boundaries. Live concurrent
sessions and a new answer lifecycle are not exercised by file-level verification.
Genuine overlapping file/index conflicts still block only the affected operation;
no general concurrent-writer permission or automatic integration is introduced.
Compiler implementation and durable semantic approval gates remain unchanged.
