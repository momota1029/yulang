# Approved answer

Question ID: 2026-10-12-nested-apply-reference-membership
Question revision: 1
Approved draft ID: 2026-10-12-nested-apply-reference-membership-a1
Approved draft revision: 1
Draft history locator: questions/2026-10-12-nested-apply-reference-membership/answer-draft.md
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): 28d4d7b88 (question baseline); cf90363b9ccf (drafting)
Task/thread locator: current working conversation; external locator unavailable
Governing source/section: notes/design/2026-10-10-parent-copy-scc-intrusion.md, “Apply-result source-fragment ownership”; predecessor approved answer, “Proposed decision and authorized scope”

## Exact approved draft content

# Answer draft — non-authoritative, not an approved answer

Question ID: 2026-10-12-nested-apply-reference-membership
Question revision: 1
Draft ID: 2026-10-12-nested-apply-reference-membership-a1
Draft revision: 1
Predecessor/history: none
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): 28d4d7b88 (question baseline); cf90363b9ccf (drafting)
Task/thread locator: current working conversation; external locator unavailable
Governing source/section: notes/design/2026-10-10-parent-copy-scc-intrusion.md, “Apply-result source-fragment ownership”; predecessor approved answer, “Proposed decision and authorized scope”

## User wording and provenance

The user selected option A with the exact wording: “Aです。” This was in response to the explanation of the nested-Apply membership question in the current conversation. No external thread locator is available.

## Interpretation

The user selects recursive inclusion of resolved Name occurrences within an Apply's callee/argument source subtree. If an Apply contains a nested Apply, the outer Apply result also records names used inside that nested Apply. The answer concerns source-reference incidence for SCC construction, not runtime reachability or equality between Apply result rows.

## Proposed decision and authorized scope

Select option A for nested Apply membership. For `my use f = f(0)(0)`, both Apply results record a Value-reference edge to the actual binder row for `f`: `R1 → F` and `R2 → F`. The outer Apply recursively includes resolved Name occurrences in its nested callee subtree. Syntactic containment alone does not add an edge from `R2` to `R1`; edges point to the binder of a resolved Name occurrence.

This selects only whether nested Apply operands are included when determining the resolved Names owned by an Apply source fragment. It does not decide Lambda, Block, wrapper, or local-initializer boundaries; authorize implementation; alter parent/copy intrusion; or prove reference transport, SCC qualification, soundness, principality, complete Call, effects, or F5 replacement.

## Approval request

Please explicitly approve draft `2026-10-12-nested-apply-reference-membership-a1`, revision 1, if this wording captures the decision.

Pending status: all unintegrated answer files/history remain unstaged and uncommitted, including after approval. The answerer never mutates Git; the questioning primary discovers, validates, and integrates the matching bundle. Corrections to an approved answer require a new linked question and renewed approval.

## Explicit approval provenance

User approval quote: “OK.”
Approval message/thread locator: current working conversation; external locator unavailable
Approval date/context: 2026-10-12, user approved the displayed complete draft in this conversation
Revision explicitly approved: 2026-10-12-nested-apply-reference-membership-a1, revision 1
Authorized scope: select option A for nested Apply membership as stated in the approved draft; no additional implementation or scope change

Publication: finalized locally after explicit approval. Leave unstaged and uncommitted. The questioning primary validates and integrates the matching bundle.
