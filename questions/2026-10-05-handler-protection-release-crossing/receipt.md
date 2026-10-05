# Receipt — approved handoff integrated; decision not yet recorded as durable authority

Question ID: `handler-protection-release-crossing`
Question revision: `q1`
Draft ID/revision: `handler-protection-release-crossing-answer/d1`
Approved answer locator: `approved-answer.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Current relevant source revision(s): `dfd49d1b14a9aba922bb0278ca7c1bfac8061058`, with the clarified notation source in commit `659eb05646bb95f10a991bbb9cefdee55721eea1`
Task/thread locator: unavailable: no stable thread locator is exposed
Governing source/section: as listed in `question.md` q1

Local answer discovery: complete finalized q1/d1 bundle discovered in this worktree on 2026-10-05.
Pre-integration validation and bundle stability: identities and revisions matched; approved answer embeds the complete d1 text (allowing its one separator newline), quotes `OK`, and explicitly identifies d1 as one of the three drafts approved together. Bundle hashes were recorded immediately before integration; selected paths had no worktree delta after the integration commit.
Approved handoff commit: `28dddc75f`, on the intended branch
Current files match committed question/draft/answer: yes; `git diff HEAD -- <bundle paths>` is empty after commit.

## Validation

The governing source files cited from `dfd49d1` remain unchanged through `d0a57e847`. The later `659eb0564` change clarifies that `'e` attribution and slot departure are independent, release removes only protection while retaining attribution, and ordinary eligibility remains separately governed. It does not decide release timing or lifetime, so it does not contradict q1 or the approved answer. The q1/d1 identities agree across the bundle, and the approved answer contains the full saved d1 text and explicit approval provenance. The approved choice is release only at an actual outward crossing after intervening computation/handler processing, with release scoped to the same target view while the original receiver remains active; it does not select handlers, grant capture, consume events, or subtract row support. No implementation authority is granted.

## Outcome and reason

Accepted and integrated as a provenance-bearing user decision. It closes the requested transition/lifetime choice but leaves derivation of an executable release predicate from typed-boundary evidence open.

Application/consumption record: not yet applied to a durable authority record.
Repository records/gates: update governing design/theory/task records only after required independent review. `tasks/current.md` and the inference theory map currently have overlapping staged/worktree edits from concurrent work, so synchronization is deferred at those exact paths.
Affected work waiting: handler-release bridge, related principality claims, and production implementation remain gated.
History retained: `question.md`, `answer-draft.md`, and `approved-answer.md` are committed together in `28dddc75f`.
User-facing rejection returned: not applicable.
