# Branch join source review

`/root/branch_join_prover` and `/root/branch_join_source` inspected the source
case/catch join and the candidate direct-boundary plan. Independent reviewer
`/root/catch_return_review` confirmed the bounded runtime and constraint facts
and reviewed the handoff. Revision 1 SHA-256 was
`25a0aafb29f486823853fcd031314691ecd644278ad4906b5e4b9dd6a2c6856c`.
The primary corrected a source-line locator and qualified continuation capture:
a binder captures the raw suffix; a wildcard continuation discards it. The
reviewer accepted revision 2 SHA-256
`ad43ac0ce2b8bde0e7a6ac0b233fe90e0eb5a072a9bbc155ad8fe33d7e868291`.

A Catch with no value arm that normally returns forwards the entire received
scrutinee value; the native candidate adds its value constraint to the result
only for that case. With a value arm, that arm supplies the result. Operation
arms and escaping requests require separate paths; this bounded evidence does
not prove arbitrary source/native equivalence or whole-world identity.
The original generator passes the scrutinee and arm sites to `branchJoin`,
but that alone does not construct a typed scrutinee/result insertion.

The candidate source-core plan runs an arm body followed by its actual direct
boundary before returning the result. That boundary may itself request or fail;
equal endpoint types do not authorize discarding it or replacing its original
identity. Case/Catch are source-rule constructors, not automatically the
auxiliary relational Union node. Their local operator interpretation and any
connection to a clause catalogue require separate construction. Current-world,
forwarded handler, raw continuation and result interfaces remain distinct.

The reviewer inspected source and existing tests, without running them. No Lean
theorem, new source semantics or production permission was delivered. R159,
independent logical admission and source/native correspondence remain open;
parent delta is zero. All workers stopped with no repository writes.
