# Approved answer

Question ID: 2026-10-12-definition-root-value-reference-forwarding
Question revision: 1
Approved draft ID: 2026-10-12-definition-root-value-reference-forwarding-a1
Approved draft revision: 1
Draft history locator: questions/2026-10-12-definition-root-value-reference-forwarding/answer-draft.md
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): c4224d749 (question baseline); 53f8b165ebbf (drafting)
Task/thread locator: current working conversation; external locator unavailable
Governing source/section: notes/design/2026-10-10-parent-copy-scc-intrusion.md, “Value-reference SCC clarification”, “Apply-result source-fragment ownership”, and “Retained boundary”

## Exact approved draft content

# Answer draft — non-authoritative, not an approved answer

Question ID: 2026-10-12-definition-root-value-reference-forwarding
Question revision: 1
Draft ID: 2026-10-12-definition-root-value-reference-forwarding-a1
Draft revision: 1
Predecessor/history: none
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): c4224d749 (question baseline); 53f8b165ebbf (drafting)
Task/thread locator: current working conversation; external locator unavailable
Governing source/section: notes/design/2026-10-10-parent-copy-scc-intrusion.md, “Value-reference SCC clarification”, “Apply-result source-fragment ownership”, and “Retained boundary”

## User wording and provenance

The user selected option 1 with the exact wording: “1”. This was in response to the explanation of the definition-root Value-reference forwarding question in the current conversation. No external thread locator is available.

## Interpretation

The user selects definition-root ownership: when a definition is published, its root Value row owns the resolved Name references in its source-owned initializer/body. A nested declaration's initializer references belong to that nested declaration's own root. This records source references on definition roots; it does not make definition roots equal to Lambda, Block, or Apply rows.

## Proposed decision and authorized scope

Select option 1 for definition-root Value-reference ownership. For the example in the question, the published outer definition root `O` owns its reference to nested definition root `E`, and `E` owns its reference to `O`, giving `O → E` and `E → O`. The independently selected Apply-result rule continues to give the Apply result rows their own Name-reference edges, such as `R → O` and `S → E`. These are separate incidences; subtype relationships or row identity assumptions do not create them.

This selects only how definition publication contributes resolved Name references to the Value-reference graph. It does not define nested Apply fragment membership, prove transport or SCC qualification, authorize implementation, or establish intrusion equality soundness/principality, complete Call, effects, public cutover, or F5 replacement.

## Approval request

Please explicitly approve draft `2026-10-12-definition-root-value-reference-forwarding-a1`, revision 1, if this wording captures the decision.

Pending status: all unintegrated answer files/history remain unstaged and uncommitted, including after approval. The answerer never mutates Git; the questioning primary discovers, validates, and integrates the matching bundle. Corrections to an approved answer require a new linked question and renewed approval.

## Explicit approval provenance

User approval quote: “OK.”
Approval message/thread locator: current working conversation; external locator unavailable
Approval date/context: 2026-10-12, user approved the displayed complete draft in this conversation
Revision explicitly approved: 2026-10-12-definition-root-value-reference-forwarding-a1, revision 1
Authorized scope: select option 1 for definition-root Value-reference ownership as stated in the approved draft; no additional implementation or scope change

Publication: finalized locally after explicit approval. Leave unstaged and uncommitted. The questioning primary validates and integrates the matching bundle.
