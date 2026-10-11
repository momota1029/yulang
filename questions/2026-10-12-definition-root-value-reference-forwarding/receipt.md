# Decision receipt

Question ID: 2026-10-12-definition-root-value-reference-forwarding
Question revision: 1
Approved draft: `2026-10-12-definition-root-value-reference-forwarding-a1`, revision 1
Integrated bundle commit: `eb46991e5`
Branch: `research/simple-sub-intrusion`

## Validation

- The finalized answer names the matching question and draft revisions and
  records the user's explicit approval quote, “OK.”, for option 1.
- The approved draft body exactly matches the current `answer-draft.md`.
- The question baseline `c4224d749` is an ancestor of the current branch. The
  governing parent-copy design section is unchanged from that baseline.
- The question, draft, and approved answer were committed together in
  `eb46991e5`; no other question directory was included.

## Outcome and scope

Definition publication assigns the resolved Name references in a definition's
source-owned initializer/body to its root Value row. A nested declaration's
initializer references belong to that nested declaration's root. This does not
identify definition roots with Lambda, Block, or Apply rows, and it does not
prove source construction, transport, SCC qualification, or intrusion equality
preservation. The user-approved scope is now recorded in the authoritative
intrusion design after a bounded pre-write `spec_auditor` review. The reviewer
found no semantic issue; its minor request to state the remaining Apply-boundary
distinctions was incorporated. No implementation was authorized, and no
compiler code or tests changed.

Governing design integration: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`
at commit `2245e8576`.
