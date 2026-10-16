# Answer draft — non-authoritative, not an approved answer

Question ID: `receive-negative-formal-pair-formation`
Question revision: `q1`
Draft ID: `receive-negative-formal-pair-formation-answer`
Draft revision: `r1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): baseline `e0fa94e509d28eea9aa7d5884b5fa2b060363ca4`; question premises and source hashes recorded in `question.md`
Task/thread locator: unavailable; the active conversation exposes no stable message/thread locator
Governing source/section: `rules/design-authority.md` (“Design status” and “Approval and implementation gate”); `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2, 3–4; `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5

## User wording and provenance

Exact relevant wording from the active conversation (no stable thread locator is available):

> 1. B．きちんと`a -> b -> [e] c`を扱えるようにすべき

## Interpretation

The user selects option B: prepare a narrowly scoped source-definition proposal for independent review and later explicit user approval. The proposal must cover the source form `a -> b -> [e] c` as requested, including the negative paired interface and its actual lower/residual association on the returned-function/local-use route. This wording sets a requirement for the proposal; it does not itself select the detailed typing rule, adopt new semantics, approve an implementation, or close a proof gate.

## Proposed decision and authorized scope

Select **B**. Luna may prepare a narrowly scoped source-definition proposal that explains how the form `a -> b -> [e] c` is formed and how its paired negative interface `Q_a+ / Q_a-`, ordinary formal edges, and actual lower contributions are associated with any reached subtraction residual through the authentic `f () -> install(g) -> local use/freshening -> g ()` route.

The proposal must preserve the approved distinction between local subtraction permission, constraint-derived inflow, and residual; it must not treat permission as inflow, force the negative input to `{E}`, erase additional effects or unknown tails, or merge independent provider and residual lineages. It must account for the separate call demands `J1` and `J2` and the original annotation occurrence.

This authorizes proposal drafting only. It does not adopt the rule, decide its detailed formalization, authorize compiler changes, or close `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` or any dependent proof or production gate. Independent review and later explicit user approval remain necessary before adoption; implementation remains gated on that process and the resulting proof/source correspondence.

## Approval request

This is draft `r1`, not an approved answer. Explicitly approve this displayed revision to publish it as the answer to question revision `q1`, or identify the changes needed.

Pending status: all unintegrated answer files/history remain unstaged/uncommitted, including after approval. The answerer never mutates Git; the questioning primary discovers, validates and commits the matching approved bundle. Corrections to an approved answer require a new linked question and renewed approval.
