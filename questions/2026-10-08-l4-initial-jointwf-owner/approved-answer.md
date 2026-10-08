# Approved answer: owner of the authentic initial JointWF context

Question ID: `l4-initial-jointwf-owner`
Question revision: `q1`
Approved draft ID: `l4-initial-jointwf-owner-answer`
Approved draft revision: `d1`
Draft history locator: `questions/2026-10-08-l4-initial-jointwf-owner/answer-draft.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): current source branch HEAD recorded in question q1 as `1d593506b94a73a26f3d050f9302dd220464a98f`
Task/thread locator: unavailable; this conversation has no exposed stable thread identifier
Governing source/section: `questions/2026-10-08-l4-initial-jointwf-owner/question.md`, “Requested scoped decision” and “Options and consequences”; `notes/design/2026-10-08-source-generalize-definition.md` §§2–3

## Exact approved draft content

# Answer draft: owner of the authentic initial JointWF context

Question ID: `l4-initial-jointwf-owner`
Question revision: `q1`
Draft ID: `l4-initial-jointwf-owner-answer`
Draft revision: `d1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): question q1 records current source branch HEAD `1d593506b94a73a26f3d050f9302dd220464a98f`
Task/thread locator: unavailable; this conversation has no exposed stable thread identifier
Governing source/section: `questions/2026-10-08-l4-initial-jointwf-owner/question.md`, “Requested scoped decision” and “Options and consequences”; `notes/design/2026-10-08-source-generalize-definition.md` §§2–3

## User wording and provenance

Exact user wording in this conversation: 「1かな．差分コンパイルみたいなことがしたいので……」

## Interpretation

I interpret 「1」 as selecting option 1, caller-owned authentic initial context. The stated reason is that retaining or supplying the relevant context from the compilation host fits the goal of incremental/differential compilation. This does not by itself decide a Rust type or API, context caching/invalidation rules, validation/failure behavior, or any other open architecture detail.

## Proposed decision and authorized scope

Select option 1: the compilation caller owns and supplies the authentic initial `JointWF` context, including its complete evidence and dependencies. Yulang's compilation and inference path must accept that supplied context and retain or reference it wherever the selected source formation and publication steps require it. An opaque `valid` flag or an invented empty-world marker does not satisfy this requirement.

The reason for this choice is to support incremental compilation: the host can manage and reuse the relevant initial context across compilation work. This answer selects the context owner only. It does not define how reuse, versioning, or invalidation works, and it does not select a concrete API or storage representation.

This choice does not authorize compiler implementation by itself. The caller/context API and its validation and lifecycle rules still need a reviewed durable design. It does not resolve the other source/HIR correspondence, inference, export, principality, resource/failure, or F5 replacement gates listed in question q1.

## Approval request

Please explicitly approve draft `l4-initial-jointwf-owner-answer` revision `d1` if this captures the intended choice and scope. If the incremental-compilation rationale should also select context reuse or invalidation behavior, that requires a separate scoped decision rather than being inferred here.

Pending status: this is a draft only. It is not an approved answer and remains unstaged and uncommitted.

## Explicit approval provenance

User approval quote: 「OK」
Approval message/thread locator: this conversation; stable external locator unavailable
Approval date/context: 2026-10-08; user approved immediately after the displayed d1 draft
Revision explicitly approved: `l4-initial-jointwf-owner-answer` revision `d1`
Authorized scope: select option 1, caller-owned authentic initial context, with the rationale of supporting incremental compilation; does not select reuse/invalidation policy or authorize implementation.

Publication: finalized locally after explicit approval. This file and the matching draft remain unstaged and uncommitted for the questioning primary to discover, validate, and integrate.
