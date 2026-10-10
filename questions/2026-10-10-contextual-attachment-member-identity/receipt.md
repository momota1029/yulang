# Integrated answer receipt

Question ID: `contextual-attachment-member-identity`
Question revision: `q1`
Draft ID: `contextual-attachment-member-identity-a1`
Draft revision: `a1`
Approved-answer: `approved-answer.md`
Integration commit: `d86d50dd2`
Worktree/branch: `/home/momota1029/rust/yulang`, `research/simple-sub-intrusion`
Validation date: 2026-10-10

## Validation

- Question, draft and approved answer identify the same q1/a1 handoff.
- The approved answer embeds the exact current answer draft byte-for-byte.
- The explicit approval quote is “よいと思いますが，Simple-subから離れ始めているので後で注意しておきますね”. It follows the displayed draft and approves option 1 within its exact scope.
- The answer's source baseline `f352d289e5c689629d1991caa85ef7d922c82bf6` is an ancestor of integration commit `d86d50dd2`.
- At handoff validation, `contextual-attachment-admission-design.md` §§1–4 and `annotation-effect-hygiene-integration.md` §§1–4 matched the q1 baseline. A later direct user correction changed §1's callback-example framing: the former output is retracted, while the general annotation polarity policy and the attachment-grouping premises remain unchanged.
- The bundle hashes at staging validation were:
  - `question.md`: `93e89daab0db3ec348cdac066b731a8d82b8bd6bcbc4e9977e192f5c00f24ace`
  - `answer-draft.md`: `3a42aaab100b48dbcd46c2aa8c3513a76a6eef53fd26f7d93786a0f0aae54d39`
  - `approved-answer.md`: `eabdf28e19860fb0206c123aa0e81c39d24f66a5539e885a7f9e398a901092ca`

All three current files equal their committed versions at `d86d50dd2`.

## Outcome and scope

Option 1 is integrated: members of one exact concrete annotation occurrence
share one attachment identity while retaining their own ordinals and resolved
effect operands. Distinct occurrences and fresh local instances use distinct
identities. The durable scope is recorded in
`notes/design/2026-10-10-contextual-attachment-admission-design.md` §3.1 and
indexed from `notes/design/INDEX.md`.

The user also warned that work was starting to move away from Simple-sub. This
receipt carries that concern forward: the decision only settles identity
grouping within the approved Simple-sub contextual carrier; it authorizes no
alternate solver, proof-driven restriction, formal-row admission, or public
cutover. No implementation is claimed by this receipt.
