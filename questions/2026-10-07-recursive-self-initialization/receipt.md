# Receipt — validated handoff; governing source applied, compiler enforcement pending

Question ID: `recursive-self-initialization`
Question revision: `q1`
Draft ID/revision: `recursive-self-initialization-answer` / `d1`
Approved answer locator: `approved-answer.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Current relevant source revision(s): question source revision `3209e890a0d3c6d96121f64339e9513905f54875`; current branch through `4b5ae128e` (REC_INIT premises unchanged in listed governing files)
Task/thread locator: unavailable; neither conversation exposes an identifier
Governing source/section: `question.md` q1; `notes/theory/successor-proof-obligations.md` REC_INIT and RAW_SOURCE; listed design/progress clauses in q1

Local answer discovery: complete `approved-answer.md` found in the exact original worktree on 2026-10-07.
Pre-integration validation and bundle stability: identities, revisions, exact draft inclusion, explicit `OK` quote and approval scope validated; SHA-256 hashes rechecked immediately before staging.
Approved handoff commit: `a814bc76aa107f2ffb7aae9cb2e2887c5b078792` on the intended branch.
Current files match committed question/draft/answer: verified by comparing each working file with its path at commit `a814bc76`.

## Validation

The question, current draft and approved answer all identify `recursive-self-initialization` q1 and answer draft d1. `approved-answer.md` contains the entire saved draft exactly, followed by provenance recording the user's explicit `OK` after the complete draft was displayed. The original worktree, branch and source revision match q1. The relevant REC_INIT premises remain unchanged since q1; the only change to the listed theory source since then concerns the separate REC_DESC route.

The approved choice excludes only the exact singleton `my f = f` from the executable-source envelope, preserves its existing F4 inference result, and requires deterministic rejection before execution or self-read. It does not select runtime error, nontermination or a value-producing rule, and does not extend to other recursion forms or general `Never` expressions.

## Original handoff outcome and reason

Accepted as a valid user-approved semantic handoff and integrated without changing its content. The answer is not yet applied to compiler behavior. Its scope does not independently authorize implementation or production cutover; a reviewed governing-source record and the existing inference proof/cutover gates remain required before implementation.

Application/consumption record: handoff validated and recorded; no compiler or design-authority source changed.
Repository records/gates: `REC_INIT` and `RAW_SOURCE` remain open pending a reviewed governing-source update; soundness, principality, source adequacy and production cutover gates remain unchanged.
Affected work waiting: implementation of this exact pre-execution rejection rule and any source-adequacy claim that depends on it.
History retained: q1, `answer-draft.md` d1 and `approved-answer.md` in this directory.
User-facing rejection returned: not applicable.

## Governing-source application, 2026-10-07 round 3

The primary revalidated `question.md`, `answer-draft.md` and
`approved-answer.md` byte-for-byte against the handoff commit
`a814bc76aa107f2ffb7aae9cb2e2887c5b078792`, including the exact saved draft
inside the approved answer. None of those three files was changed.

The reviewed [exact singleton governing rule](../../notes/design/2026-10-07-recursive-self-init-executable-boundary.md)
now applies q1/d1 to execution acceptance. Independent compiler-referee and
spec-auditor both passed its exact source rule, source-envelope inversion,
unchanged F4 `Never` inference and pre-execution/no-self-read proof. The
primary accepted the reviews. Authority remains this already approved q1/d1
answer; the new record makes no wider recursive-initialization decision.

The canonical DAG records `REC_INIT_SELF` CLOSED for this exact source
subcase. Aggregate `REC_INIT` and `RAW_SOURCE` stay open for their other
premises. The original handoff's pending-governing-source prerequisite is
retired only for q1. Compiler recognition of the exact original envelope and
enforcement before initialization are still unimplemented; the new default-off
shadow carries structural candidates with both premises explicitly pending.
Production cutover remains prohibited. See the
[round-3 review/integration record](../../notes/progress/2026-10-07-successor-round3-review.md).
