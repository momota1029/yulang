# Decision receipt

Question ID: 2026-10-12-nested-apply-reference-membership
Question revision: 1
Approved draft: `2026-10-12-nested-apply-reference-membership-a1`, revision 1
Integrated bundle commit: `30e22fc4c`
Branch: `research/simple-sub-intrusion`

## Validation

- The finalized answer names the matching question and draft revisions and
  records the user's explicit approval quote, “OK.”, for option A.
- The approved draft body exactly matches the current `answer-draft.md`.
- The question baseline `28d4d7b88` is an ancestor of the current branch. The
  governing parent-copy design section is unchanged from that baseline.
- The question, draft, and approved answer were committed together in
  `30e22fc4c`; no other question directory was included.

## Outcome and scope

An Apply result recursively owns resolved Name occurrences in its
callee/argument source subtree, including a nested Apply subtree. Thus for
`f(0)(0)`, `R1 → F` and `R2 → F`; containment does not add `R2 → R1`. This does
not authorize implementation or prove source construction, transport, SCC
qualification, or intrusion equality preservation. The user-approved scope
is now recorded in the authoritative intrusion design after a bounded pre-write
`spec_auditor` review. The reviewer found no semantic issue; its minor request
to state the remaining Lambda, Block, wrapper, and local-initializer boundaries
was incorporated. No implementation was authorized, and no compiler code or
tests changed.

Governing design integration: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`
at commit `2245e8576`.
