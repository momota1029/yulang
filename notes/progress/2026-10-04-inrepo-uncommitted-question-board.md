# Repository question-board switch

Date: 2026-10-04
Branch: research/simple-sub-intrusion
Authority: [user-requested successor](../design/2026-10-04-inrepo-uncommitted-question-board.md), sections 1–5

## Decision and scope

The user's current explicit instruction replaces the external board with
questions inside Yulang that remain uncommitted until the user opens an
answering conversation and approves its organized answer draft. The answering
primary then commits the selected question/draft/answer. This supersedes the
external-location and answering-Git restrictions; original approval,
freshness, history and authority safeguards remain.

Architect advisory `inrepo_board_design_check` identified no remaining user
decision. Isolated pre-write `spec_auditor` (`inrepo_board_scope_review`)
found no blocking, major or minor issue. User authorization is recorded in the
successor; the same requested choices did not require another approval prompt.

## Delivery

- Repository-local `questions/README.md`, nested `AGENTS.md` and four blank
  templates, all infrastructure intended for tracking.
- Active rule and root/workflow/Git routing protect pending question
  directories from all checkpoint staging/commits and keep them Git-visible.
- Answer publication and Git integration require exclusive primary writer
  ownership handoff; a working goal can continue independent read-only work
  during that handoff. No concurrent-writer exception is introduced.
- The working primary consumes only fresh exact approved content committed
  with its question/draft on the intended branch, then records a receipt.
- The former external AGENTS/README now redirect to the repository board.
  Only bootstrap/templates existed there; they were preserved. No live question
  or approval was created, deleted, migrated or committed by this delivery.
- Predecessor/index status and current-task navigation are synchronized.

## Review and verification

Mode M2: one architect advisory, one implementer, pre-write scope review and
one fresh spec closure review. Convergence: no accepted blocking/major findings.
Verification budget: file/reference/index/diff inspection only; zero compiler
tests/builds or performance measurements.

Final isolated `spec_auditor` review (`inrepo_board_closure`) found one accepted
major defect: nested board instructions unconditionally assigned the answering
role and therefore prohibited the working primary's question/receipt/bootstrap
writes. A single bounded implementer repair made role selection conditional on
the actual task and preserved working-primary ownership. Fresh isolated delta
review (`inrepo_board_role_delta`) closed the finding with no new issue; all
other previously clean delivery surfaces were carried forward.

Checks completed:

- `git diff --check` on the eight modified routing/rule/task/status files — passed.
- Inline `python3` file/reference/visibility inspection — passed: sixteen
  repository files exist; forms are blank/non-authoritative with question
  identity/revision; `questions/` contains only bootstrap/templates; pending
  question paths are not Git-ignored; active routes no longer use the external
  path; old entrypoints redirect and four external templates are preserved.
- Scoped final diff/index inspection excludes concurrent inference-record
  changes and any live pending question from this infrastructure commit.

No compiler build/test or performance measurement was run. Live runtime behavior
and an actual question/answer commit were not exercised. Required task/design
and progress records are synchronized; no record update is intentionally deferred.

## Next action and limits

Publish the next real unresolved question under `questions/<unique-id>/` and
leave it uncommitted. The user can find it with Git status and open a separate
answering thread against that exact worktree. No Git ignore rule, background
watcher, automatic pause or resume mechanism was added. A commit remains a
handoff marker, not approval evidence by itself. Live answer publication,
ownership transfer and goal runtime behavior remain unverified; independent
review and compiler implementation authority gates remain in force.
