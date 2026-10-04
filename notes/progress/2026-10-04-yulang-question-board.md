# Yulang question-board delivery

Date: 2026-10-04
Branch: research/simple-sub-intrusion
Authority: [approved workflow](../design/2026-10-04-yulang-question-board.md), sections 1–5

## Scope and approval

The user selected a Yulang-only board and explicit approval after an answering
primary organizes a draft. The external four-file workflow was independently
reviewed by `spec_auditor` (`question_board_review`), then approved by the user's
`良さそう` response to the proposal and creation request. No compiler decision
or implementation authority is added.

## Delivery

- Active policy: `rules/question-board.md`.
- Routing: root `AGENTS.md`, `rules/INDEX.md`, `rules/workflow.md` and
  `notes/design/INDEX.md`.
- Current-task navigation: `tasks/current.md`, preserving its inference goal.
- Local board: `/home/momota1029/.local/share/yulang/question-board/`, with
  `AGENTS.md`, `README.md` and four blank forms under `templates/`.

The local directory was absent before creation; no existing board data was
overwritten. It is outside Git and the compiler worktree. Its entrypoint allows
the answering primary to operate independently and write only answer files.
The tracked design and rule preserve the workflow; the local bootstrap and
future live handoffs remain local files. No watcher, notification mechanism,
automatic goal resumption or fictitious question/approval was created.

## Review and verification

Mode: M1 implementation of a confirmed workflow, with one `implementer` and
one fresh `spec_auditor` closure review. The primary owns record updates and
Git integration. Convergence requires no accepted blocking or major finding.
Verification budget: file/reference and diff inspection only; zero tests,
compiler builds and performance measurements.

Fresh isolated `spec_auditor` closure review (`question_board_closure`) found
no blocking, major or minor issue in policy, routes, entrypoint and templates.
The primary accepted the clean report; record-only updates close through
primary inspection without another panel.

Checks completed:

- `git diff --check -- AGENTS.md rules/INDEX.md rules/workflow.md notes/design/INDEX.md tasks/current.md` — passed.
- `python3` inline file/reference inspection — passed: eight repository paths
  and six local bootstrap files exist; all four blank forms carry question
  identity/revision and non-authoritative markers; local README and delivery
  record links resolve; no live question or approval is seeded.
- Primary scoped diff and record inspection — preserves the active inference
  objective and excludes concurrent inference-progress work from staging.

Builds and tests were omitted because this is a Markdown/manual-workflow
delivery with no compiler changes. Runtime handoff behavior remains unverified.

## Next action and limits

When an actual unresolved user decision arises, publish a complete question.
Open a separate answering thread from the board directory and approve its
displayed draft before finalization. The working primary validates the handoff
at turn start and before dependent work and records consumption or rejection.

Existing running threads are not assumed to reload changed instructions.
Stopped goals may need explicit resumption in their original thread. Actual
live question/approval/consumption and cross-thread lifecycle behavior were not
exercised by bootstrap. No repository records are intentionally deferred.
