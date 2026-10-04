# Questioner receipt: role-indexed effect-row meaning

Question ID/revision: `function-effect-row-denotation/q1`
Answer draft: `function-effect-row-denotation-answer/d1`
Approved answer: `approved-answer.md`
Original worktree/branch: `/home/momota1029/rust/yulang`, `research/simple-sub-intrusion`
Source baseline: `c3fe10151e6e73fda428ade0a30224cecfd8bb4b`
Integration commit: `cd7df4c0ef2603e9d566c9b0ec2580cab85ee975`

## Validation

- The question, draft and approved answer identify the same q1/d1 handoff,
  branch, worktree and source baseline.
- The full `Exact approved draft` body in `approved-answer.md` is byte-for-byte
  equal to `answer-draft.md`.
- The finalized answer records the user's explicit `OK` for the complete d1,
  identifies the answering context and unavailable message locator, and limits
  approval to the exact stated semantic scope.
- The source baseline is the branch's prior `HEAD`. The governing source files
  listed in the question are unchanged between that baseline and the
  integration point.
- Immediately before staging, all three bundle files were rehashed and
  matched their validation hashes. Only `question.md`, `answer-draft.md`, and
  `approved-answer.md` were staged. After commit, each working file was
  compared byte-for-byte with its committed version.

## Outcome and remaining scope

Accepted for the scoped effect-row decision: covariant and contravariant row
positions have different meanings; the covariant mixed row is an allowance
that requires the shared abstract component also to occur contravariantly;
the contravariant `['e, write int]` case constrains any matching
`write 'a` in `'e` to be compatible with `write int` (the supplied example is
`int <: 'a`); and when that shared component reaches a covariant position it
does so with `write int` removed for the selected deep-handler case. A
candidate principal type for a shallow handler is recorded only as
tentative.

The answer does not define all family-argument variance, the complete
annotation-to-occurrence/membership rule, shallow-handler principal typing,
surface parser spelling, or a new evidence carrier. It does not establish
soundness, principality, production endpoint adequacy, or implementation
authority. The next step is independent semantic/design review, then a narrow
governing design addendum that preserves these limits before any dependent
implementation work.
