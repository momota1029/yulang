# R170 Rust permission-owner integrity — frozen writer handoff

Assignment: `R170-EFFECT-PERMISSION-OWNER-INTEGRITY-RUST`.
Sprint contract: `tasks/agent-loop/sprints/effect-permission-owner-integrity-r170.md`.

## Outcome

Restored the read-only permission adapter to take route, term arena, permission
state, registrations, LocalSource recipe, and source HIR from one
`InferenceSession`. The adapter authenticates the retained route incidence,
registration label, unique Lambda recipe and occurrence, source Lambda parameter,
raw Function argument effect row, captured FreshUse representative, and mapped
native argument row before asking that session's effect state for the permission.
The receiver again carries provider family/member, selected arm, operation,
permission member, and Catch-owner joins through the same evidence structs. The
permission lookup scans retained entries by their explicit `registration` label,
rejects duplicates, and cross-checks the selected entry against the Catch-held
permission. This does not use a formal ordinal to index the sparse permission
vector.

The adapter remains dead-code/evidence-only. No consumer, Catch subtraction,
constraint or inference mutation, semantic change, or promotion was added. This
is not parent-theorem closure or source-to-execution proof.

## Source mapping

- `candidate_scheme.rs:452-498`: reconstruct one incidence from this route's
  retained graph, terms, and effect-row map; require a positive native Function
  with the exact retained argument-effect child.
- `candidate_scheme.rs:501-590`: seal route, store, effect state, registrations,
  recipes, and LocalSource inside one `InferenceSession`; join the unique
  retained context origin and permission by registration/Lambda identity; check
  the raw row and current captured representative separately from the mapped
  FreshUse row.
- `candidate_receiver.rs:225-238, 604-620`: preserve provider/member and
  permission-member evidence in the projection and Catch request.
- `candidate_receiver.rs:1870-1898`: select the unique permission by its
  explicit registration label and rejoin the permission pointer/index, source
  owner, occurrence, annotation row, provider family/member, view, selected arm,
  and operation identity.
- `candidate_receiver.rs:5138-5177`: authenticate operation origin and selected
  arm, then match the retained permission and concrete provider family/member.
- `candidate_receiver.rs:4866-4878`: carry the captured provider and permission
  evidence into the Catch request.

## Frozen artifacts and diff

Input worktree SHA-256 at assignment:

- `crates/yu-solver/src/candidate_scheme.rs`:
  `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470`
- `crates/yu-solver/src/candidate_receiver.rs`:
  `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`

Frozen output SHA-256:

- `crates/yu-solver/src/candidate_scheme.rs`:
  `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e`
- `crates/yu-solver/src/candidate_receiver.rs`:
  `5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade`

Changed hunks relative to the input: `candidate_scheme.rs` restores the
session-owned adapter and adds a route-provider/registration-owner equality
check. `candidate_receiver.rs` restores the removed projection/request fields
and provider/Catch ownership checks, and replaces positional permission lookup
with unique explicit-label lookup. Relative to `HEAD`, the only receiver diff is
the preserved six-line duplicate-guard deletion already committed in
`a811c9d25`; no other receiver hunk was changed. The unrelated dirty-file
content was preserved.

## Evidence, checks, and limits

Reused the earlier session-owned construction in `3429a3e5f` and its retained
raw-row/captured-representative checks in `685b97bd1`, plus the current source
contracts in `candidate_effect.rs` (`FormalEntryPermission` and
`bind_formal_entry_permission_use`). Rejected the assigned split-input adapter:
caller supplied route/store/effect state/registration/occurrence could be mixed
across sessions. Rejected positional `permissions.get(registration)`: retained
permissions are sparse and identified by their explicit `registration` field.

Only `git diff --check --` on the two leased source files was run; it passed.
No Cargo command, Rust build, test, target/cache/environment creation, or
persistent scratch was used. No scratch paths were created. The assignment's
1200-second maximum was not exhausted; measured runtime was not available in
this child interface. Requested model/effort: Luna/high implementer. Observed
model/effort: unavailable to this writer interface, so not independently
asserted.

The lane stopped after the scoped source repair and handoff. The adapter is
still unconnected and provisional; an independent compiler referee must review
the frozen source hashes before Luna adjudicates. No known disposable scratch
remains. New path: this handoff only.
