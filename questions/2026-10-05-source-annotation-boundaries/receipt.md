# Receipt — approved handoff integrated; decision not yet recorded as durable authority

Question ID: `source-annotation-boundaries`
Question revision: `q1`
Draft ID/revision: `source-annotation-boundaries-answer/d1`
Approved answer locator: `approved-answer.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Current relevant source revision(s): coverage audit `a38e79e6157f641674103073ce1527831d3480eb`; concrete-composition obstruction `80b5749f0`; governing compatibility design unchanged through `0ab7620e167f190691a9ec50fde507d039265aa4`
Task/thread locator: unavailable: no stable thread locator is exposed
Governing source/section: as listed in `question.md` q1

Local answer discovery: complete finalized q1/d1 bundle discovered in this worktree on 2026-10-05.
Pre-integration validation and bundle stability: identities and revisions matched; approved answer embeds the complete d1 text (allowing its one separator newline), quotes `OK`, and explicitly identifies d1 as one of the three drafts approved together. Bundle hashes were recorded immediately before integration; selected paths had no worktree delta after the integration commit.
Approved handoff commit: `28dddc75f`, on the intended branch
Current files match committed question/draft/answer: yes; `git diff HEAD -- <bundle paths>` is empty after commit.

## Validation

The cited governing design sources remain unchanged from their stated revisions. Current HIR/syntax worktree edits do not remove the relevant premise: expression annotation syntax is recognized, while `yu-hir` module lowering still reports `UnsupportedExpression` for the unsupported expression path before solver constraints are generated. The q1/d1 identities agree across the bundle, and the approved answer embeds the exact saved d1 and explicit approval provenance. The approved decision includes binding annotations, argument annotations, and expression `as Type`; each successful boundary checks the current endpoint directly against its target, exports the target plus local realization evidence, preserves earlier evidence, and disallows unbounded intermediate concrete adaptations without a source boundary. No implementation or permanent exclusion policy is approved.

## Outcome and reason

Accepted and integrated as a provenance-bearing user decision. This selects annotation-boundary behavior but leaves source adequacy and the annotation-bearing recursive-group proof open.

Application/consumption record: not yet applied to a durable authority record.
Repository records/gates: update governing design/theory/task records only after required independent review. `tasks/current.md` and the inference theory map currently have overlapping staged/worktree edits from concurrent work, so synchronization is deferred at those exact paths.
Affected work waiting: annotation-bearing source adequacy, recursive-group adequacy, and production elaboration remain gated.
History retained: `question.md`, `answer-draft.md`, and `approved-answer.md` are committed together in `28dddc75f`.
User-facing rejection returned: not applicable.
