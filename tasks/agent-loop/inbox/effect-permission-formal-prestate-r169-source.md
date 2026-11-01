# R169 source handoff — FormalEntry pre-state and publication

Status: source-qualified construction map; no Rust code changed and no Rust
build/test was run. The reviewed source audit is
`effect-permission-formal-entry-current-rust-audit.md`, SHA-256
`7004a57f14b79c73450c68431743ef7401232195b7d63c85d55f76f04eabb33d`.

## Frozen bytes and owner reads

- `crates/yu-solver/src/candidate_source.rs`
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
- `crates/yu-solver/src/candidate_effect.rs`
  `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`
- `crates/yu-solver/src/lib.rs`
  `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`

All three Rust files were clean at inspection and remain the exact declared
source dependencies. No dirty/quarantined file was read.

## Collector and exact action payload

At `candidate_source.rs:1323–1327`, the Lambda collector clones the actual
`parameter.annotation`; if its type has an effect row, it looks up
`formal_registrations` by that same `parameter.id` and queues
`Action::FormalEntry { registration, annotation, occurrence, scope }`. The
occurrence is the Lambda expression occurrence and the scope is read from the
selected registration. The executor at `candidate_source.rs:2469–2475` passes
that exact action payload to `candidate_formal_entry_annotation`.

This producer edge is necessary for correspondence. The constructor validates
the passed annotation's owner and validates the LocalSource Lambda's occurrence
and formal ID, but does not independently compare the annotation payload with
`Lambda.parameter.annotation`. The Lean event relation must therefore derive
the action from the actual parameter record and retain its annotation, not add a
second independently chosen annotation table.

## Constructor branch as state transitions

At `candidate_effect.rs:1991–2012`, the method reads the action annotation's
effect row, rejects more than one symbolic variable, reads the exact registered
formal, and checks computation role, owner, scope, parameter-recipe identity,
source-owner lookup and exact LocalSource Lambda occurrence/formal ID. It also
checks that this parameter recipe has no formal domain and that this
registration has no retained entry permission. The registered entry effect
must exist.

If `row.concrete` is nonempty, `:2015–2039` reserves storage and copies the
entire concrete vector in iteration order into one `FormalEntryPermission`.
The record carries the same registration, recipe position, formal identity,
occurrence, source owner, scope, annotation position, source-row position and
entry effect. Duplicates are copied, not set-normalized. If concrete is empty,
no permission record is prepared or appended.

If one symbolic variable is present, `:2041–2045` finds its scoped effect row
and admits the two equalities at occurrence slot 45 before publication. Then
`:2047–2051` increments retained byte accounting and appends the prepared
permission. The resource sample at `:2059` is later and can fail after the
append. A model of `Err => unchanged` at the method boundary is therefore
unsound. Route-owned checkpoints record permission vector length and bytes
(`candidate_effect.rs:480–501, 660–695`); whether the containing caller owns a
rollback is a separate transition, not a constructor-local law.

## Same-record reader and consumer boundary

`lib.rs:18341–18470` has a read-only
`internal_formal_permission_incidence`. It authenticates the exact internal
use, unique Internal route/fact, target-root computation registration,
unique lambda recipe/origin, source Lambda, original negative effect entry and
lambda fact, then retrieves the unique retained permission for that same
registration, Lambda occurrence, target owner and entry. It is explicitly
`allow(dead_code)` because no consumer is connected. This audit establishes no
Catch subtraction, successful Suppress execution or residual correctness.

## Lean mapping and falsifiers

The proof lane may model the source projections as finite raw lists because
`ComputationPermissionEntryR39` is itself a finite-list constructor model, but
must derive the action and pre-state reads from the event input. The constructor
trace must re-run guards as events and derive R39 `prepare`; it must not carry
`Valid` or `prepare` as an accepted-transition premise. A successful nonempty
row must derive `permissionFor` and equality with the exact appended record.

Falsifiers: a separately supplied annotation that differs from the Lambda
parameter annotation; already-retained registration used as pre-state; lost or
reordered duplicate atoms; empty concrete row published as a permission; or a
post-publication resource failure modeled as unchanged state.

Source event mapping: `candidate_source.rs:1323–1327, 2469–2475`,
`candidate_effect.rs:1991–2063`, `lib.rs:18341–18470`. No semantic-policy or
production authority is inferred from this source map.
