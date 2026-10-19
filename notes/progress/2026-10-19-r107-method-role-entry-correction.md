# R107 closeout: source ownership fixed, type review blocks execution

Status: **FAILED_TO_ACHIEVE_CONTRACT_PREREQUISITE; NOT_RUN**.

R107 continued the finite R106 method/role source-entry outcome. It restored
the existing `declarations` binding, tied the selected member's original
ancestor chain to the associated same-parse `ImplDeclaration`, and added a
recursive comparison of original CST raw children—including tokens and
trivia—with retained positions for parent, ordinal, node/token status, kind and
range. The exact 148-byte/no-final-LF source and prior assertions were
preserved. Fresh pre-edit spec review found CLEAN; post-output spec review also
found CLEAN and confirmed both R106 ownership/compile findings' intended
repairs, while preserving the conditional evidence boundary.

A fresh compiler/source review found two new **BLOCKING** static type issues in
the frozen test:

1. `assert_eq!(declaration.node(), impl_node)` compares borrowed
   `&SyntaxNode` and owned `SyntaxNode`; the associated view returns a borrowed
   node while `impl_node` is owned.
2. In the raw child slot search, `.as_ref()` turns `child.as_node()`'s
   `Option<&SyntaxNode>` into `Option<&&SyntaxNode>`, which is compared with
   `Option<&SyntaxNode>`.

These block compilation of the `yu-hir --lib` test target before `--exact`
filtering. R107 requires stopping on a new BLOCKING finding, so Luna did not
repair either line or run the authorized command. No test/build/compiler/runtime
command or formatter was run.

## Frozen evidence

- R107 contract SHA-256:
  `6d9cde2feb3b8f91c82cf11a872ea04e03d157ab73ccb53b7b044e9a88082f43`.
- Pre-edit spec review: CLEAN; recorded at
  `tasks/agent-loop/inbox/20261019-r107-spec-review.md`.
- Test file SHA-256:
  `3519e4a5e3cf3fa2a855125f6ea739e6765fea0dd34b0c2c881088a129b259f4`.
- Implementation handoff SHA-256:
  `85ce90b283b5298e60786c511a39e8f82c9c77141638e3003f0d2ac02c5e3d2f`.
- Post-output spec review: CLEAN; recorded at
  `tasks/agent-loop/inbox/20261019-r107-post-spec-review.md`.
- Compiler/source review: BLOCKING with two static type mismatches; recorded at
  `tasks/agent-loop/inbox/20261019-r107-compiler-review.md`.
- R107 command: **NOT RUN**; retry is prohibited under R107.

The R106 test compile defect is corrected and its source ownership gap is
closed in the frozen text. R100-ENTRY remains unobserved because no command has
run. R100 P2/P3/P4, body checking, method lookup/dispatch, result `2`, original
Simple-sub/evaluator claims and R85 adoption remain OPEN. The proof remains a
conditional argument, not an observed source-entry result.

The next authorized method/role step must be a new, narrow packet correcting
the two borrowed/owned reference comparisons, followed by fresh output review
and the first authorized run. It must preserve R106 and R107 failure receipts.

The persistent goal still balances six independent effect-hygiene fronts,
method/role proof work, and early ordinary/effectful runnable source execution.
R105's wrong/sibling permission CLI result remains its own finite observation.
Neither effect semantics nor any theorem or production gate is promoted here.

All producer and reviewer writes are stopped. R107 outputs remain frozen under
the new-packet boundary. Luna owns current-state reconciliation and the next
authorized lease.
