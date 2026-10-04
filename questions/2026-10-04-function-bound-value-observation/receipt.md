# Receipt: typed Function-bound observations

Question ID: `function-bound-value-observation`
Question revision: `q1`
Draft ID/revision: `function-bound-value-observation/r1`
Approved answer locator: `questions/2026-10-04-function-bound-value-observation/approved-answer.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Current relevant source revisions: `13378f6bf1b9c503332127e8157a9112ff07e3a4` (question premise); `b64a506f6916ece87ed7926692eec6db70dcc529` (approved handoff)
Task/thread locator: unavailable: no repository thread locator is exposed
Governing source/section: question q1; `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` §§2.4–4; `notes/progress/2026-10-04-callback-local-abstraction-boundary.md` §§2, 4–6; `notes/design/2026-10-04-production-callback-endpoint-generation-draft.md` §4

Approved handoff commit: `b64a506f6916ece87ed7926692eec6db70dcc529` on the intended branch and `origin/research/simple-sub-intrusion`.
Current committed question/draft/approved-answer files match `HEAD`, validated with `git diff --quiet HEAD -- questions/2026-10-04-function-bound-value-observation`. This receipt is a new working-primary file awaiting its coherent commit.

## Validation

- The commit is a child of the question's relevant source revision `13378f6bf1b9c503332127e8157a9112ff07e3a4`; the question, draft, and answer are all added in that one commit.
- Question ID/revision `function-bound-value-observation/q1` matches the approved answer. The approved answer names draft `r1`, embeds its exact content, and the committed `answer-draft.md` matches that content.
- The answering primary records the user's decision quote: 「ではAで答えましょう．」 The publication instruction is recorded as: 「ちょっとそこは予想してなかった．勝手にそこだけコミットしてればいいと思うけど」. It explicitly authorizes this scoped publication; no approval of implementation or design-authority changes is claimed.
- The answer selects typed observations for callback adequacy: concrete data-value identity/correlation is omitted; value types, typed interface events/requests, continuations, origins, and existing `nu,K,D` relations are retained. It preserves `zero : any -> int` and explicitly leaves projection adequacy and production endpoint correspondence open.
- The source premises remain current, and the handoff is fresh and on the intended branch. No conflicting receipt or prior consumption exists.

## Outcome and reason

Accepted and consumed once within the answer's exact scope. The callback proof/denotation boundary now uses the approved typed observation projection. This does not establish that the scalar local abstraction is adequate for higher-order callbacks, does not prove production endpoint correspondence, and does not authorize compiler implementation or edits to existing design authority.

Application/consumption record: `tasks/current.md` records the selected observation boundary and the remaining review/proof gates.
Repository records/gates: the answer is user-approved; independent semantic review and recording in a governing design remain required before implementation. The source-generated theorem package is Reviewed and conditional, with no implementation authority; the production callback design remains Draft. The active callback gate is typed-projection preservation plus actual production endpoint realization.
Affected work waiting: no longer waiting on this choice; dependent theorem/design work may proceed only under the scoped typed-observation contract. Compiler implementation remains unauthorized.
History retained: question, r1 draft, approved answer, and this receipt remain together in the question directory.
User-facing rejection returned: not applicable.
