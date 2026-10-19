# R107 post-output compiler/source review

Reviewer: `/root/r107_compiler_review`, independent, read-only.
Contract SHA-256: `6d9cde2feb3b8f91c82cf11a872ea04e03d157ab73ccb53b7b044e9a88082f43`.
Result: **BLOCKING — NOT CLEAN; do not execute the R107 command.**

Verified the contract, test SHA
`3519e4a5e3cf3fa2a855125f6ea739e6765fea0dd34b0c2c881088a129b259f4`, handoff
SHA `85ce90b283b5298e60786c511a39e8f82c9c77141638e3003f0d2ac02c5e3d2f`,
five pinned compiler dependencies and four supplied R106 proof/closeout/review
hashes. Initial findings came from contract/test/API inspection before reading
the implementation self-explanation.

## BLOCKING 1: incompatible node comparison

Target: `crates/yu-hir/src/tests/shadow_method_role_source.rs:237`.
`assert_eq!(declaration.node(), impl_node)` compares borrowed `&SyntaxNode`
with owned `SyntaxNode`. `AssociatedRoleImplSource::node` returns
`&'a SyntaxNode` at `crates/yu-hir/src/shadow.rs:479`; `source_node` returns an
owned clone. These reference levels do not satisfy the required equality
implementation. Under renewed authority, the minimum correction is
`assert_eq!(declaration.node(), &impl_node)`.

## BLOCKING 2: extra reference in original-slot lookup

Target: same test file, line 305. `child.as_node()` returns
`Option<&SyntaxNode>`; `.as_ref()` makes the left side `Option<&&SyntaxNode>`
while `Some(&impl_node)` is `Option<&SyntaxNode>`. The predicate cannot
typecheck. Under renewed authority, the minimum correction is to remove
`.as_ref()`.

Both findings violate the R107 compilability outcome and its explicit
uncompilable-assertions falsifier. The whole test target typechecks before the
exact filter, so no observation can run while either finding remains. These are
static Rust/API findings; no compiler command ran.

The original R106 undefined-name defect is repaired, and the added ownership
checks substantively address its missing correspondence. Original ancestry
uses same-parse keys up to the exact impl key/node; the associated view is tied
to that identity; recursive comparison derives original `children_with_tokens`
and checks count/order/ordinal/parent/node-token/kind/range while recursively
tying each node to its retained key. The exact source literal is unchanged and
matches the 148-byte/no-final-LF fixture. The handoff keeps all
executable-binder, resolution, Apply, dispatch, result-2 and parent-theorem
boundaries OPEN.

No files changed; no tests/builds/compiler/runtime/formatter/Git or executable
probes ran. Read-only inspection and hashing only. Reviewer returned this
report by message; Luna recorded it here.
