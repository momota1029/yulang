# R108: fix the two exact method/role source-entry comparisons

Status: CANDIDATE, revision 1. Primary: Luna `/root`.

## Fixed outcome

Resolve only the two static type blockers found by fresh R107 compiler/source
review, freeze the corrected test, obtain fresh independent review, then run the
original exact method/role source-entry test once. Do not revise any other
assertion or source behavior.

The exact source stays 148 bytes with SHA-256
`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`, without
a final LF. R106 and R107 remain closed `NOT_RUN`; preserve their reports and
output hashes as historical evidence.

## Authorized changes

Only `crates/yu-hir/src/tests/shadow_method_role_source.rs` may change, and only
these two reference-level corrections:

1. Compare associated borrowed `declaration.node()` with `&impl_node` rather
   than the owned `impl_node`.
2. Compare `child.as_node()` directly to `Some(&impl_node)`; remove the extra
   `.as_ref()` that creates `Option<&&SyntaxNode>`.

No assertion, source literal, expected behavior, method/role semantics,
ownership invariant, production code, test name or unrelated formatting may
change. If either correction requires another edit, owner, dependency or API,
stop without command.

Reuse R106's frozen conditional source/consumer argument and R107's frozen
ownership assertions only at their actual premises. Do not create a proof
lane. The exact-source entry remains unobserved until the authorized command
passes. No executable binder, method resolution, dispatch, ordinary Apply,
candidate/runtime admission, result `2`, R100 P2/P3/P4, Simple-sub/evaluator
closure, R85 adoption or production promotion follows from this packet.

## Frozen direct inputs

| Input | SHA-256 |
|---|---|
| R107 revision-1 contract | `6d9cde2feb3b8f91c82cf11a872ea04e03d157ab73ccb53b7b044e9a88082f43` |
| R107 test before this packet | `3519e4a5e3cf3fa2a855125f6ea739e6765fea0dd34b0c2c881088a129b259f4` |
| R107 compiler/source finding | `02be1fd1884abb627da378fd175217221fff37fa4d6a744b386675cc18286255` |
| R107 post-spec review | `45273a0f23810cd86fd27dca9d3fcaa25c64cf01d2e8e41848113b9e9a521955` |
| R106 conditional proof note | `b7591ef9aefbe6d8f7694afc2a2b967fd9c4489756d78b52eb7d474aad2523cd` |
| `crates/yu-hir/src/shadow.rs` | `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |

All listed pins must match. R107 post-spec CLEAN is preserved only as semantic
scope review; the compiler/source review BLOCKING findings remain authoritative
until these exact comparisons are corrected and freshly reviewed.

## Exact leases and verification

Test-only implementation, Luna/high, cap 60 seconds:

- `crates/yu-hir/src/tests/shadow_method_role_source.rs`
- `tasks/agent-loop/inbox/20261019-r108-implementation.md`

Fresh pre-edit spec delta review, cap 30 seconds:
`tasks/agent-loop/inbox/20261019-r108-spec-review.md`.
Fresh post-output spec review, cap 30 seconds:
`tasks/agent-loop/inbox/20261019-r108-post-spec-review.md`.
Fresh compiler/source review, cap 120 seconds:
`tasks/agent-loop/inbox/20261019-r108-compiler-review.md`.
Luna closeout: `notes/progress/2026-10-19-r108-method-role-entry-reference-fix.md`.

Reviewers inspect only exact pins and frozen outputs, return read-only reports
by message, and stop. Luna records attributed receipts at the exact paths.
Producers/reviewers run no test, build, compiler/runtime/CLI, formatter or Git
command. After the corrected bytes and both CLEAN post-output reviews freeze,
Luna may run exactly once, with no retry or substitute command:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib tests::shadow_method_role_source::exact_role_impl_member_source_reaches_original_occurrences -- --exact --nocapture
```

Any nonzero result ends the packet without repair. No build-only check is
authorized.

## Resources, stops and breadth boundary

- Pre-edit spec: 30 seconds.
- Test-only implementation: 60 seconds.
- Post-output spec: 30 seconds.
- Compiler/source review: 120 seconds.
- Luna's one command: 120 seconds.
- Closeout: 60 seconds.
- Total cap: 420 seconds; Astra 0; no new proof allocation.

Preserve three inherited UNKNOWN identities, quarantined board lease and
legacy slot reservation. Stop on pin drift, any extra diff, any review finding,
command failure, missing owner, unknown writer or budget exhaustion.

R108 finishes this exact-source entry attempt; it does not authorize another
repair round. At closeout, rotate the next bounded outcome toward one of the
six still-independent effect-hygiene fronts or early ordinary/effectful source
execution. Keep proof-backed method/role work in the parent goal without
letting this single test or any one effect front monopolize the sequence.
