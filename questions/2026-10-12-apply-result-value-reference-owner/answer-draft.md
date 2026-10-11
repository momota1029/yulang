# Answer draft — non-authoritative, not an approved answer

Question ID: 2026-10-12-apply-result-value-reference-owner
Question revision: 1
Draft ID: 2026-10-12-apply-result-value-reference-owner-a1
Draft revision: 1
Predecessor/history: none
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): f6c2f4cbe (question baseline); 59b0e7f684577e62457cfd6ec87d2b1b46a3f731 (answer drafting)
Task/thread locator: current working conversation; external locator unavailable
Governing source/section: notes/design/2026-10-10-parent-copy-scc-intrusion.md, “Value-reference SCC clarification”; notes/design/2026-10-11-yulang-inference-top-level-principles.md, §§1–3

## User wording and provenance

The user responded to the A/B explanation: “Aでしょ……” and then “はい” after the assistant restated the proposed A decision and offered to make it explicit. These messages are from the current working conversation; no external thread locator is available.

## Interpretation

The user selects option A: an Apply result Value row records resolved Name references occurring in that Apply source fragment. This records source-computation incidence for SCC construction; it does not claim that the runtime returned object points to every name used during computation. The later “はい” confirms this interpretation of the selected answer.

## Proposed decision and authorized scope

Select A for Apply-result Value adjacency. Every resolved Name in the Apply source fragment contributes an edge from the Apply result row to the actual binder Value row, before and after Call dispatch. For example, `konst 1` contributes `r → konst` even when the returned provider is the literal `0`. This edge records the source computation's reference incidence, not runtime object reachability.

The edge must be retained explicitly from the Apply source constructor; it must not be inferred from Function demand ports, subtype comparison, or returned-provider identity. This decision selects only the Apply-result Value-reference equation for SCC adjacency. It does not change the approved parent/copy intrusion operation, complete Call typing, effect semantics, or supported source domain, and it does not itself prove the source construction or transport implementation correct.

## Approval request

Please explicitly approve draft `2026-10-12-apply-result-value-reference-owner-a1`, revision 1, if this wording accurately captures the decision. The earlier “はい” confirmed the A decision but preceded this complete identified draft, so it is not treated as approval of this draft artifact.

Pending status: all unintegrated answer files/history remain unstaged/uncommitted,
including after approval. The answerer never mutates Git; the questioning primary
discovers, validates and commits the matching approved bundle. Corrections to
approved answers require a new linked question and renewed approval.
