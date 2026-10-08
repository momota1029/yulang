# Approved answer: native ordinary Direct consumer architecture

Question ID: `native-direct-consumer-architecture`
Question revision: `q1`
Approved draft ID: `native-direct-consumer-architecture-answer`
Approved draft revision: `d1`
Draft history locator: `questions/2026-10-08-native-direct-consumer/answer-draft.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): question q1 records source revision `6982402afa95f93552bdd5954d22c852b27b3f92`; reviewed proposal SHA-256 `1947eff96d4450f33f446988e75f5d818bf5d75b641bdbfbfbb0d0dc2e6aae60`
Task/thread locator: unavailable; this conversation has no exposed stable thread identifier
Governing source/section: `questions/2026-10-08-native-direct-consumer/question.md`, “Requested scoped decision” and “Options and consequences”; `notes/design/2026-10-08-native-direct-consumer-plan.md`

## Exact approved draft content

# Answer draft: native ordinary Direct consumer architecture

Question ID: `native-direct-consumer-architecture`
Question revision: `q1`
Draft ID: `native-direct-consumer-architecture-answer`
Draft revision: `d1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): question q1 records source revision `6982402afa95f93552bdd5954d22c852b27b3f92`; reviewed proposal SHA-256 `1947eff96d4450f33f446988e75f5d818bf5d75b641bdbfbfbb0d0dc2e6aae60`
Task/thread locator: unavailable; this conversation has no exposed stable thread identifier
Governing source/section: `questions/2026-10-08-native-direct-consumer/question.md`, “Requested scoped decision” and “Options and consequences”; `notes/design/2026-10-08-native-direct-consumer-plan.md`

## User wording and provenance

Exact user wording in this conversation: 「1かな」

## Interpretation

I interpret this as selecting option 1 for question q1: adopt the reviewed flat-arena architecture as the direction for a checker-only implementation gate. This does not approve implementation, a public API, a production inference path, or F5 replacement.

## Proposed decision and authorized scope

Select option 1: adopt the reviewed flat-arena checker proposal as the architecture direction for a finite ordinary `Direct(u,V)` proof checker against supplied native public roots. Proceed with the specified next design work: map the exact caller and local-law owners, and set numeric resource limits before implementation.

This is a checker-only architecture decision. It does not approve a public API, source/application semantics, inference routing, production use of this checker, or replacement of F5. The native public-root producer, source bridge, and caller must still be established before the checker can serve as a production inference path. The selected `Direct` semantics remain unchanged.

## Approval request

Please explicitly approve draft `native-direct-consumer-architecture-answer` revision `d1` if this captures the intended choice and scope.

Pending status: this is a draft only. It is not an approved answer and remains unstaged and uncommitted.

## Explicit approval provenance

User approval quote: 「OK」
Approval message/thread locator: this conversation; stable external locator unavailable
Approval date/context: 2026-10-08; user approved immediately after the displayed d1 draft
Revision explicitly approved: `native-direct-consumer-architecture-answer` revision `d1`
Authorized scope: select option 1, adopting the reviewed flat-arena checker proposal as the direction for a checker-only implementation gate; no implementation, public API, source/application semantics change, inference routing, production use, or F5 replacement is approved.

Publication: finalized locally after explicit approval. This file and the matching draft remain unstaged and uncommitted for the questioning primary to discover, validate, and integrate.
