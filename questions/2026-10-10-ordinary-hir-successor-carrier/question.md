# Question: ordinary-hir-successor-carrier

Question ID: `ordinary-hir-successor-carrier`
Question revision: `q1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision: `47beb83c9` (reviewed proposal and synchronized records)
Task/thread locator: unavailable; stable conversation identifier and exact message timestamp are not exposed
Governing sources: `rules/design-authority.md`; `notes/design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md` §§Association and recovery authorities, Admission and identity; `notes/design/2026-09-20-hir-direct-root-expression-slice.md`; `notes/design/2026-10-10-simple-sub-legacy-withdrawal.md`

## Requested scoped decision

Approve or reject the reviewed internal architecture in
[`notes/design/2026-10-10-ordinary-hir-successor-carrier.md`](../../notes/design/2026-10-10-ordinary-hir-successor-carrier.md)
for the ordinary HIR bridge required by successor inference.

This decision concerns only the supplementary carrier's ownership, result
representation, and formation timing. It does not reopen Simple-sub
let/generalization, parent-copy SCC intrusion, or the selected annotation
polarity policy, and it does not authorize changing ordinary header admission.

## Premises

- The active user objective requires the successor to be used through ordinary
  inference entrypoints and requires actual F5 replacement.
- `lower_module` currently does not retain the candidate `LocalSource` carrier.
- Directly enabling the existing opt-in lowerer changes ordinary header
  admission, diagnostics, failure behavior, and occurrence allocation, contrary
  to current HIR authority.
- The attached proposal leaves existing HIR items, resolutions, errors,
  diagnostics, recovery handling, and occurrence ordinals unchanged. It stages
  source identities atomically and records an explicit unsupported carrier
  outcome without falling back to F5.
- A specification audit and independent compiler-referee review found no
  remaining findings after two minor wording repairs. No implementation or
  compiler verification has run.

## Options and consequences

1. **Approve q1 and the linked reviewed proposal.** The primary may implement
   that exact behavior-preserving carrier gate, with focused HIR and ordinary
   collector verification. This does not authorize header-admission expansion
   or claim complete ordinary inference/F5 cutover.
2. **Reject q1 and state a different carrier architecture or boundary.** The
   affected HIR bridge waits; independent inference work can continue.

Requested answer: explicitly approve option 1, or reject it with the intended
alternative.

## Exact affected scope

Blocked: implementation of the supplementary carrier storage/formation in
ordinary HIR and the dependent default collector bridge.

Independent requirements remain active: complete Call, effect attachment and
hygiene, public scheme/use correspondence, soundness, principality, production
cutover, and retirement of remaining F5 consumers. This question does not waive
or close any of them.

Keep this directory unstaged and uncommitted until an explicit approved answer
is finalized and validated by the questioning primary.
