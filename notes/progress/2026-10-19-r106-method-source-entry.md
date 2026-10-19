# R106 closeout: method/role source entry stopped at review

Status: **FAILED_TO_ACHIEVE_CONTRACT_PREREQUISITE; NOT_RUN**.

R106 intended to add one exact-source HIR observation for the R100 `SecondInt`
role/implementation fixture. The exact 148-byte source and its SHA-256
`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb` were
correctly embedded without a final LF. The test attempts to bind source nodes,
keys, ranges and retained positions for the declaration roots and the ordered
`second`, `self`, `selected` pattern occurrences plus a distinct body
`selected`. The proof correctly treats R100-ENTRY as pending until the test is
reviewed and run, and keeps R100 P2/P3/P4, body checking, dispatch, evaluation
result `2`, original Simple-sub/evaluator claims and R85 adoption OPEN.

The implementation output was not ready for the authorized command. Two fresh
independent reviewers found:

1. **BLOCKING:** in the pre-existing test at
   `crates/yu-hir/src/tests/shadow_method_role_source.rs:34–38`, the local and
   length check were renamed to `pending_declarations` while later assertions
   still reference undefined `declarations`. This is an introduced compile
   error; `--exact` does not avoid typechecking the rest of the test target.
2. **MAJOR:** the new test does not connect the member through its retained
   ancestry to the associated `ImplDeclaration`, and does not compare retained
   parent/child relationships and order against the syntax tree. It therefore
   falls short of the source ownership invariant promised by the contract and
   proof note.

The contract requires stopping on BLOCKING/major review. Luna did not run the
single authorized command and made no repair under R106. The implementation
handoff's claim that existing assertions remain is contradicted by the frozen
test bytes; that claim is not accepted. No source-entry observation has been
recorded as executed evidence, and R100-ENTRY remains open.

## Evidence and review

- R106 contract SHA-256:
  `edd6c951b46b3f1993c57b5f5cdec4928652cfb313120bd60d9e64c6ebc922bf`.
- Candidate proof note SHA-256:
  `b7591ef9aefbe6d8f7694afc2a2b967fd9c4489756d78b52eb7d474aad2523cd`.
- Proof handoff SHA-256:
  `72d386d275b032e06d35191509da49c3ab8e552eef9be01fa32cdbee80327b95`.
- Test file SHA-256:
  `1e0683edf8820e7599f196322f653ddb4698555e089e5f4f88b33ed9fae21df4`.
- Implementation handoff SHA-256:
  `bd07525b6594fa42f562ee0c2a27bba90b948404d13525fe38bdc4c54a5e8f33`.
- Fresh post-spec result: BLOCKING + MAJOR, recorded in
  `tasks/agent-loop/inbox/20261019-r106-post-spec-review.md`.
- Fresh compiler/source result: MAJOR, recorded in
  `tasks/agent-loop/inbox/20261019-r106-compiler-review.md`.
- Pre-edit spec review was CLEAN; receipt:
  `tasks/agent-loop/inbox/20261019-r106-spec-review.md`.
- The R106-only focused command was **not run**. There was no retry, build,
  formatter, runtime or CLI command.

The next permissible method/role action requires a new frozen contract that
restores the prior test and adds direct implementation-declaration ownership
and retained parent/child/order assertions. Proof can reuse R106's conditional
argument, but exact R100-ENTRY remains unobserved until the revised test passes
its fresh review gate and single authorized run.

The parent goal remains broad: six separate effect-hygiene fronts, proof-backed
method/role behavior, and runnable ordinary/effectful source execution remain
in scope. R105's bounded wrong/sibling-permission CLI result is unchanged. No
effect front or method/role gate is promoted by R106.

Changed R106 paths are the revision-1 sprint contract, this closeout, the
candidate proof note and handoff, the test file and implementation handoff,
pre/post review receipts, and Luna-owned current scheduling state. All producer
and reviewer writes have ceased. All outputs remain frozen pending a separate
authorized correction packet.
