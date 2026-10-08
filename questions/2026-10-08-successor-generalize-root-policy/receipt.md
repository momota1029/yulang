# Integration receipt: successor-generalize-root-policy/q1

Question ID: `successor-generalize-root-policy`
Question revision: `q1`
Draft ID/revision: `successor-generalize-root-policy-answer/a1`
Approved answer: `approved-answer.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Question source revision: `7eab2767f`
Integration commit: `ec5e36c91`
Task/thread locator: current thread; stable external locator unavailable
Governing source/section: FVIEW §§1–5; source-contracts §§2–3, 5.3; redesign charter Gates D–E

## Validation

- `question.md`, `answer-draft.md`, and `approved-answer.md` identify q1/a1 and
  the same worktree and branch. The approved file embeds the complete draft
  byte-for-byte.
- `approved-answer.md` records the explicit approval quote 「OK．承認します．」
  and limits approval to the stated design direction. It explicitly does not
  claim that sufficiency is proved or authorize concrete semantics, algorithms,
  or compiler implementation.
- The question's source revision `7eab2767f` is an ancestor of the bundle
  commit. Its three named governing design documents are unchanged between
  that revision and the local integration commit.
- The separate upstream-only commit `2ea53e3dd` was inspected. Its source
  Generalize definition leaves actual public projection obligations separate;
  it does not select or contradict this answer's public export target. That
  commit is not integrated into this local branch, so no claim about its
  integration is made here.
- The exact q1/a1 bundle was committed alone at `ec5e36c91`. Current question,
  draft, and approved answer match their committed versions.

## Outcome and scope

Option 2 is accepted for the first concrete source-Generalize rule proposal:
design the actual public target as an abstracted/displayable scheme with only
the additional use-time information proved necessary. Do not retain the full
source relation as the public target merely by renaming it. Determine the
extra information and prove safety, approved inference behavior, principality,
and generalization/instantiation preservation for the transformed target.

This is a research/design direction, not a proof that the target is sufficient,
not adoption of the existing common-allowance proposal, and not authority to
implement or remove open gates. It does not change source membership, Option 2,
production conformance, or the active F5-replacement objective.

Application/consumption: guides the next transformed-export construction and
its proof obligations; no semantics or implementation has been changed.
Repository records/gates: the design direction is recorded here. A reviewed
governing design proposal and the independent transformation, principality,
production, and implementation gates remain outstanding.
Affected work waiting: construction and proof of the first transformed public
export; dependent implementation remains unauthorized.
History retained: q1 question, a1 draft, approved answer, and this receipt.
User-facing rejection returned: not applicable.
