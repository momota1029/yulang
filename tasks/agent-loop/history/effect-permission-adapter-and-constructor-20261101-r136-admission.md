# R136 admission

Sprint contract: `tasks/agent-loop/sprints/effect-permission-adapter-and-constructor-20261101-r136.md`.

The dispatcher selected the exact Rust adapter type mismatch at committed
`candidate_scheme.rs:451–506` as the smallest source repair that can be
reviewed without consuming R111's unavailable compile gate. A parallel
read-only Rust source map identified a separate nested `FormalPermission`
constructor/consumer gap and the exact variance/path constructor law. R136
admits a bounded Lean structural theorem for that law while preserving the
original source soundness and effect-hygiene parents as OPEN.

Working-tree `candidate_effect.rs`, `candidate_receiver.rs`,
`candidate_scheme.rs`, and `shadow_apply.rs` have pre-existing dirty edits.
No worker may read or modify those edits. Runtime `machine.rs` and
`receiving.rs` remain quarantined; pending untracked R103/module-supplier
artifacts remain untouched. Only Luna may later apply the exact immutable-HEAD
Rust one-line patch to the index after independent review.

Capacity reservations for the pre-existing UNKNOWN worker set were already
released under the authenticated receipt in `current.json`; this admission
does not change worker observations, path leases, or count those identities a
second time. At admission, the live agent roster contained Luna and completed
prior children only; no RUNNING/WAITING child required notification.

No source/compiler/Lean/test execution has occurred at admission. The Rust
baseline and exact target hashes are frozen in the contract. The proof lane
must use the pinned project and report theorem types plus complete axiom
audits. Fresh independent reviews remain required before either result is
integrated.
