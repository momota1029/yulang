# Approved answer — finalized local handoff, non-authoritative by itself

Question ID: `ordinary-hir-successor-carrier`
Question revision: `q1`
Approved draft ID: `ordinary-hir-successor-carrier-a1`
Approved draft revision: `a1`
Draft history locator: `questions/2026-10-10-ordinary-hir-successor-carrier/answer-draft.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `47beb83c9` (reviewed proposal and synchronized records)
Task/thread locator: unavailable; stable conversation identifier and exact message timestamp are not exposed
Governing source/section: `rules/design-authority.md`; `notes/design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md` §§Association and recovery authorities, Admission and identity; `notes/design/2026-09-20-hir-direct-root-expression-slice.md`; `notes/design/2026-10-10-simple-sub-legacy-withdrawal.md`; reviewed proposal `notes/design/2026-10-10-ordinary-hir-successor-carrier.md`

## Exact approved draft content

# Answer draft — non-authoritative, not an approved answer

Question ID: `ordinary-hir-successor-carrier`
Question revision: `q1`
Draft ID: `ordinary-hir-successor-carrier-a1`
Draft revision: `a1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `47beb83c9` (reviewed proposal and synchronized records)
Task/thread locator: unavailable; stable conversation identifier and exact message timestamp are not exposed
Governing source/section: `rules/design-authority.md`; `notes/design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md` §§Association and recovery authorities, Admission and identity; `notes/design/2026-09-20-hir-direct-root-expression-slice.md`; `notes/design/2026-10-10-simple-sub-legacy-withdrawal.md`; reviewed proposal `notes/design/2026-10-10-ordinary-hir-successor-carrier.md`

## User wording and provenance

Exact user wording in this conversation: “承認すれば良いと思います”. This responds to the two options in question revision `q1`, explained immediately above in this conversation. The question's stable task/thread locator is unavailable, as recorded in `question.md`.

## Interpretation

The user chooses option 1 and intends to approve the reviewed proposal for the ordinary HIR supplementary carrier. This draft makes that approval concrete and bounded to the proposal and scope in question `q1`.

## Proposed decision and authorized scope

Approve question `ordinary-hir-successor-carrier` revision `q1` and the linked reviewed proposal `notes/design/2026-10-10-ordinary-hir-successor-carrier.md` as the architecture for the supplementary carrier used by successor inference through ordinary HIR.

The approved gate may add storage and formation of the supplementary carrier and connect the dependent default collector bridge, following the proposal's behavior-preserving design. Existing HIR items, resolutions, errors, diagnostics, recovery behavior, and occurrence ordinals remain unchanged. Source identities are staged atomically, and an unsupported carrier outcome is recorded explicitly without falling back to F5.

This approval does not authorize changing ordinary header admission, enabling the existing opt-in lowerer as the ordinary route, or claiming complete ordinary inference or F5 cutover. It does not reopen Simple-sub let/generalization, parent-copy SCC intrusion, or annotation polarity. Complete Call, effect attachment and hygiene, public scheme/use correspondence, soundness, principality, production cutover, and retirement of remaining F5 consumers remain active requirements.

Implementation must follow the reviewed proposal and applicable design-authority process. The proposal does not become permission to expand beyond this exact carrier gate.

## Approval request

Approve draft `ordinary-hir-successor-carrier-a1`, revision `a1`, with the decision and scope written above.

Pending status: all unintegrated answer files/history remain unstaged and uncommitted, including after approval. The answerer never mutates Git; the questioning primary discovers, validates and commits the matching question/draft/answer bundle. Corrections to approved answers require a new linked question and renewed approval.

## Explicit approval provenance

User approval quote: “承認”
Approval message/thread locator: this conversation, immediately following display of draft `ordinary-hir-successor-carrier-a1` revision `a1`; stable conversation identifier and exact message timestamp unavailable
Approval date/context: 2026-10-10, user explicitly approved the displayed revision
Revision explicitly approved: `ordinary-hir-successor-carrier-a1`, revision `a1`
Authorized scope: option 1 and the carrier gate exactly as stated in the approved draft content above

Publication: finalized locally after explicit approval. This file and its draft remain unstaged and uncommitted. The questioning primary discovers and validates them, rechecks bundle stability, and alone commits the matching question, exact approved current draft and answer. The answerer performs no Git mutation.
