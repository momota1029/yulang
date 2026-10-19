# R107: complete and run the exact method/role source-entry check

Status: CANDIDATE, revision 1. Primary: Luna `/root`.

## Fixed outcome

Complete the R106 test-only source-entry observation, which did not run because
fresh review found an introduced compile error and incomplete declaration/member
ownership checks. Preserve the exact R100 fixture, existing expectations, and
R106's bounded source-entry scope. Then run the exact focused test once, but only
after fresh independent spec and compiler/source reviews are CLEAN.

The fixture remains exactly 148 bytes, SHA-256
`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`, with no
final LF:

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

The only code path is the existing test-only file
`crates/yu-hir/src/tests/shadow_method_role_source.rs`. First restore the
pre-R106 binding name `declarations` so its existing assertions compile. In
`exact_role_impl_member_source_reaches_original_occurrences`, add the missing
ownership evidence:

1. Starting from the exact `BindingStatement` for `my second self selected =
   selected`, follow its original syntax parents to the `ImplDeclaration` node
   supplied by the same-parse associated declaration view. Require identity by
   the original source key/node, not matching spelling or kind alone.
2. For the implementation declaration and its subtree containing the member,
   header, target pattern, ordered `self`/`selected` tails, body and body
   occurrence, compare original syntax parent/child relationships, raw child
   order/ordinal, kind and ranges with their same-artifact retained
   `PositionId` relationships. Derive expected relationships from original
   syntax and its raw child sequence, not from the retained tree itself.
3. Preserve exact source spelling/ranges, same-parse key ownership, distinct
   formal/body `selected` occurrences, and all pre-existing assertions.

If the exact APIs cannot establish these checks without another source owner
or production API change, stop and report the precise owner; do not expand the
pin set. No production edits or semantic/diagnostic/expected-output changes.

This finite test can establish only exact-source declaration/member syntax
entry and retained source ownership for this fixture. It establishes no
executable HirParameterIds, lexical binder resolution, body checking, method
lookup, selection, dispatch, ordinary Apply, candidate/runtime admission, or
result `2`. R100 P2/P3/P4, original Simple-sub/evaluator claims, and R85
adoption remain OPEN. Reuse R106's frozen conditional proof as argument only;
do not create a new proof lane or claim its conditional conclusion observed
until this exact command passes.

## R106 adjudication and falsifiers

R106 is CLOSED `FAILED_TO_ACHIEVE_CONTRACT_PREREQUISITE / NOT_RUN` at independent
review. R106's post-spec reviewer found both an undefined `declarations` name
and incomplete declaration/member/retained-order correspondence; its fresh
compiler/source reviewer independently confirmed the compile error. R106's
contract explicitly stopped at BLOCKING/MAJOR, and no repair or command was
made under it. Those results remain immutable. R107 authorizes the narrow
correction and complete observation described above.

Falsifiers: existing assertions remain uncompilable; member ancestry does not
reach the associated same-parse ImplDeclaration; any retained parent, raw slot,
child order, node/token distinction, kind or range differs from original
syntax; the exact source identity changes; or a new owner/API is required.
Any mismatch stops R107 without command or repair.

## Frozen direct inputs

| Input | SHA-256 |
|---|---|
| R106 revision-1 contract | `edd6c951b46b3f1993c57b5f5cdec4928652cfb313120bd60d9e64c6ebc922bf` |
| R106 candidate proof note | `b7591ef9aefbe6d8f7694afc2a2b967fd9c4489756d78b52eb7d474aad2523cd` |
| R106 closeout | `5f475d4d09208593ecb929ccfad1faa6266d3d2767a60f96df96b527159eb4bb` |
| R106 post-spec review | `c13a408a1f7ca156ee03ec8db2a39b71dc1b1a8322201a0ea7f897c5fcb2e97c` |
| R106 compiler/source review | `965f2024521e928727b54095faad73fee0b93fff3556cb8ab116c222399dbc19` |
| `crates/yu-hir/src/tests/shadow_method_role_source.rs` (pre-R107) | `1e0683edf8820e7599f196322f653ddb4698555e089e5f4f88b33ed9fae21df4` |
| `crates/yu-hir/src/lib.rs` | `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8` |
| `crates/yu-hir/src/shadow.rs` | `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-syntax/src/syntax_kind.rs` | `26d2a0ddbe1862c95c503420ded0b0d35217bee5ba9f350be9163c065c6b488d` |

Frozen R106 proof support is conditional and is not the test output. R106's
same-parse key/position and HIR/syntax owner evidence is reused only under the
listed hashes. Any changed dependency is a stop condition.

## Exact leases and command

Luna/high test-only implementation, cap 120 seconds:

- `crates/yu-hir/src/tests/shadow_method_role_source.rs`
- `tasks/agent-loop/inbox/20261019-r107-implementation.md`

Fresh pre-edit spec review, read-only, cap 60 seconds:
`tasks/agent-loop/inbox/20261019-r107-spec-review.md`.
Fresh post-output spec review, read-only, cap 60 seconds:
`tasks/agent-loop/inbox/20261019-r107-post-spec-review.md`.
Fresh independent compiler/source review, read-only, cap 120 seconds:
`tasks/agent-loop/inbox/20261019-r107-compiler-review.md`.
Luna closeout: `notes/progress/2026-10-19-r107-method-role-entry-correction.md`.

Reviewers return read-only reports to Luna; Luna records attributed receipts at
the exact paths above. Worker inspection is limited to frozen inputs and
leased outputs. No test/build/compiler/runtime/CLI, formatter or Git command
is authorized for producers/reviewers. After frozen output hashes and CLEAN
post-output reviews, Luna may execute exactly once, without retry:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib tests::shadow_method_role_source::exact_role_impl_member_source_reaches_original_occurrences -- --exact --nocapture
```

Any failure ends R107. Do not run a build-only command or substitute another
test.

## Resources and closeout

- Pre-edit spec: 60 seconds.
- Test-only implementation: 120 seconds.
- Post-output spec: 60 seconds.
- Compiler/source review: 120 seconds.
- Luna command: 120 seconds, exactly once.
- Freeze and closeout: 120 seconds.
- Total cap: 600 seconds; Astra 0; no new proof allocation.

Preserve the three inherited UNKNOWN identities, quarantined board lease and
legacy slot reservation. Keep Luna as sole Git integrator. Stop on a new
BLOCKING/MAJOR, input drift, source mismatch, missing owner, command failure,
unknown writer, or budget exhaustion. R106's failed evidence remains recorded.

## Parent goal and breadth

R107 is a necessary method/role source-entry correction, not a return to
effect-only work. Keep the six effect-hygiene fronts independent and advancing
over time, keep proof-backed method/role behavior in scope, and prioritize
ordinary/effectful runnable source paths early. Do not let any single effect
front, storage/fiber analysis, or this method/role test monopolize the
sequence. At R107 closeout, select the next bounded evidence outcome across
those fronts and source execution.
