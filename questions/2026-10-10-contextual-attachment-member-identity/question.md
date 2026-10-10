# Question: identity of members in a concrete effect annotation

Question ID: `contextual-attachment-member-identity`
Revision: `q1`
Status: awaiting an explicit user decision
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Source revision: `f352d289e5c689629d1991caa85ef7d922c82bf6`
Task/thread locator: active Yulang3 inference goal; stable conversation identifier and exact timestamp unavailable
Governing sources: `notes/design/2026-10-10-contextual-attachment-admission-design.md` §§3–6; `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–4; `rules/design-authority.md`

## Why this question is needed

The approved contextual carrier requires attachment identity to remain distinct
from effect-family identity and source spelling. Its `Attachment` record also
retains a `concrete_member_ordinal`. The source correspondence finds that the
frozen Oracle allocates one subtraction identity for a collected concrete atom
set, but the approved successor design does not say whether members of one
source annotation share an attachment identity or receive separate identities.
This matters because same-identity PUSH/POP operations can cancel, while
different identities cannot, even when their resolved effects are equal.

This asks only how to identify concrete members belonging to one annotation
occurrence. It does not ask to reopen the approved carrier/two-cycle gate, alter
the meaning of contravariant or covariant annotations, enable concrete formal
rows, or approve public/default cutover.

## Decision

For a concrete effect annotation row containing multiple concrete members, how
should contextual attachment identity be assigned?

### Option 1 — one identity per annotated atom set (recommended)

Members of one concrete annotation occurrence share one attachment identity;
each member keeps its own ordinal and resolved effect operand as payload. This
follows the inspected Oracle construction, which assigns one subtraction ID to
the collected concrete set. Separate annotation occurrences and fresh local
instances still receive separate identities.

Consequence: a source operation associated with that annotation uses the same
identity across its member set, matching the inspected Oracle grouping. The
ordinal remains available for exact diagnostics and per-member checks.

### Option 2 — one identity per concrete member

Each concrete member, identified by its ordinal, receives its own attachment
identity, even when members came from the same annotation row.

Consequence: members become independent cancellation lineages. This may diverge
from Oracle's set-wide subtraction identity and changes which contextual
operations can cancel.

### Option 3 — specify another grouping

State the intended identity unit and how its member ordinals, resolved effect
operands, and fresh local instances relate.

## Scope held while this is pending

Pause only authentic construction of contextual attachments from multi-member
effect annotations. The private expression-DAG foundation, identity-only
relations, existing symbolic-formal behavior, unrelated source/Call work, and
the overall Simple-sub/F5 replacement goal remain active. No source-level
acceptance boundary or rejection rule follows from this question.

## Required answer

Select option 1, 2, or 3, or give another concrete identity rule. This question
is pending and must remain unstaged and uncommitted until a complete approved
answer bundle is validated by the questioning primary.
