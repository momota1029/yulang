# Catch source bridge audit (2026-10-10)

## Finding

The current syntax tree already has `CatchExpression`, `CatchScrutinee`,
`CatchBlock`, and `CatchArm`. The private candidate `LocalSourceForm` has no
Catch constructor, and the current pattern parser treats each Catch arm slot as
a general `Pattern`.

The handler source shape needed by the proposed `tick::next(), k -> ...`
example is not currently admitted as a recovery-free operation pattern. The
pattern parser has no qualified operation-path/call-tail form. The source
identity map also has no Catch-arm binder owner: existing parameter identities
belong to lambdas and local identities belong to sequential initializer
bindings. Expression-side `family::member` resolution does not supply
operation-pattern resolution or resumption-binder scope.

Adding only a Catch node to `LocalSource` would retain syntax but would not
construct typed arm bodies or make callback inference possible. A useful
source bridge needs an operation-pattern parser/source constructor and
arm-owned binder/scope identities, followed by an inference consumer with the
selected contextual effect behavior. No syntax-only Catch node was added.

## Decision boundary

This audit makes no new handler syntax or inference decision. The reviewed
contextual attachment/admission proposal remains non-authoritative. Concrete
formal-row admission, complete Call, public/default inference, and F5 cutover
remain open. Existing candidate tests do not establish any of those gates.

## Evidence and limits

Read-only inspection covered `yu-syntax` case-like and pattern owners,
`yu-hir::ResolvedExpr`, `LocalSourceForm`, source-identity ownership, and
candidate preflight/collection. No source files, tests, builds, or Git refs
were changed for this audit. The previously selected annotation meanings and
parent-copy intrusion contract remain unchanged.
