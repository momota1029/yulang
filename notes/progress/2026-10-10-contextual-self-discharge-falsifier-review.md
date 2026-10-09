# Review: contextual PUSH self-discharge discriminator

Date: 2026-10-10
Reviewed artifact: `contextual-self-discharge-falsifier.md`
Artifact SHA-256: `2b81891ce53f22b842c0b68a8de52c850bf130e7040277f94b0a0339db37acd4`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Reviewer: independent compiler referee

## Result

No blocking, major, or minor findings in the assigned source-derivation scope.

- The shared symbolic Effect tail is formed by one `AnnTypeBuilder` and the
  same annotation-variable maps across the formals. This is an owning-source
  fact, not an assumed endpoint equality.
- The `accept g` demand yields the stated comparison against a separate empty
  Function filter through ordinary Function argument reversal. The absent
  argument Effect is `Row([], Top)`, so this route does not use the
  `Neg::Bot` pure-passthrough branch.
- Under the explicit premise that the retained self candidate is stored as a
  positive lower `(T+, PUSH_i[{io}])`, the later Empty registration checks
  that lower and rejects its active `io` before duplicate registration can
  suppress recursion. The drop alternative has no such lower in the compared
  local derivation. This is a valid conditional discriminator.
- At equal Effect levels, removing only the successor's same-row omission
  would select the negative side and store an upper row. That orientation does
  not establish the positive-lower premise.
- Oracle actually drops the same-variable candidate, and the current successor
  rejects explicit formal effect rows. The result is not an admitted or
  executed witness, a production unsoundness result, or a general
  contextual-equivalence theorem.

Inspected source paths include Oracle `annotation/builder.rs:386–396`,
`lowering/expr/lambda.rs:665–764,1244–1307`,
`annotation/constraints.rs:424–470,602–607,676–685,835–845`,
`lowering/expr/tail.rs:543–563`,
`constraints/machine/propagate.rs:226–233,258–263`,
`constraints/machine/bounds.rs:3213–3255,3285–3320`,
`constraints/row_effect.rs:834–848,875–932`, and successor
`candidate_extrusion.rs:443–465,675–690`.

Frozen hashes matched for the artifact, successor extrusion, and governing
authority. The materialized Oracle `annotation/constraints.rs` hash was
`3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db`.

Uninspected: parser admission, complete lowering/publication, execution and
termination, generalization/freshening, rollback, other research theorems, and
broader successor integration. No files, Git state, tests, builds, or runtime
execution were changed or used by the reviewer.

## Next gate

Keep the distinction between a source-owner-derived conditional fixture and an
actually retained lower. The next implementation/research gate must explain
this fixture using the selected successor bound orientation and filter
observation rule. Contextual self-discharge, formal rows, complete hygiene,
Call, generalization, public cutover, and F5 replacement remain open.
