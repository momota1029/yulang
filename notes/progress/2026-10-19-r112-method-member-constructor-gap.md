# R112 closeout: exact method member stops before executable HIR

Status: **CLOSED_CLEAN_FINITE_SOURCE_OBSTRUCTION**.

R112 applied R108's reviewed exact-source entry result to the original
R100-P2-MEMBER gap. For the 148-byte `SecondInt` fixture, the authentic
ImplDeclaration root enters production `plan_root`, becomes UnsupportedItem,
and `lower_plan` returns HirItem::Error before member definition-root,
parameter, body, or lexical-environment construction. Production carrier
passes accept Binding and Expression items; they do not form LocalSource for
this Error. The complete pinned LocalSource boundary accepts already supplied
Binding/DirectExpression plans and does not discover the nested implementation
member.

The frozen proof is a finite, source-qualified obstruction for this fixture
and these owners. It allows earlier availability failure, does not establish
successful whole-module publication, and does not claim repository-wide
absence of another route. A real owner-local constructor for the same member
would falsify it.

## Review and frozen artifacts

- R112 rev3 contract SHA-256:
  `ed7510f30473a7ea5c990cf12b13502e3c57e7a26e3a463ddc7402a5e17a273a`.
- Pre-edit spec review: CLEAN at
  `tasks/agent-loop/inbox/20261019-r112-pre-spec-review-rev3.md`.
- Proof SHA-256:
  `9444f51d980c2a8d01aacb407e81c4d2278f88785d6486c0d0ec696da1e48ca9`.
- Proof handoff SHA-256:
  `51811cc902a33a185fc048d2b7ca9ba093947600089ab791a0ac12dcf0dfd048`.
- Post-output spec review: CLEAN; reviewer returned the receipt by message,
  and Luna recorded it at
  `tasks/agent-loop/inbox/20261019-r112-post-spec-review.md`, SHA-256
  `abe79a7527db1a280febeea161819ac421bc629f693c8f481096f3f5a7f33f32`.
- Independent compiler/source review: CLEAN at
  `tasks/agent-loop/inbox/20261019-r112-compiler-review.md`, SHA-256
  `a11e5630191725190ecd3b167a34069ceb4570b6b66de7106b488282798c4a82`.

The proof uses production source carrier gates, not test-helper Error
branches. All nine R112 inputs were pinned and matched. No tests, builds,
compiler, runtime, CLI or formatter commands ran. No code or existing test
changed. R111 remains **CLOSED_COMMAND_FAILURE / NOT_RUN**; its test remains
FROZEN_UNVERIFIED and no retry was made.

## Parent status and next allocation

R100-P2-MEMBER remains OPEN: authentic selected-member binders, annotations,
body and environment still need an authorized producer. R85 remains Draft and
unadopted. P3/P4, method lookup/selection/dispatch, result `2`, original
Simple-sub/evaluator A/B, F1/FK1, R50, the six effect-hygiene fronts, runnable
surface work, semantic approval and production authority remain open.

The existing R100 implementation assessment remains NO_SAFE_ROLE_CODE_SLICE;
R112 grants no implementation/test lease. R111's unknown resource use was not
reset or returned. R112's 600-second cap was not extended; effective worker
models and exact aggregate CPU/wall time remain UNKNOWN where receipts do not
expose them. All producer and reviewer writes stopped. Luna retains review,
state and Git ownership.
