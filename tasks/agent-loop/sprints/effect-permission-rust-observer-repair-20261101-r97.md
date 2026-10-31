# EFFECT-PERMISSION-RUST-OBSERVER-REPAIR/20261101-R97

Status: ADMITTED. This bounded diagnostic repair does not close an effect
hygiene theorem, source/native bridge, original A/B claim, or production gate.

## Goal and fixed scope

Repair the rejected, test-only effect-permission observer so it preserves the
protected nonrecursive regression and cannot panic on valid sibling annotation
paths. Preserve solver decisions, memoization, permission semantics, SCC
qualification, refusals, outputs, source domain, and expected values.

Success requires: restore the original named nonrecursive
`tuple_formal_permissions_keep_element_paths_and_transaction_ownership` test
and its assertions; retain any recursive transport fixture under a separate
name; remove test-observer assumptions that every symbolic effect memo event
has a formal-constructor ID; cover traced and untraced sibling/root annotation
paths; pass the focused feature-correct Rust test gate; receive a fresh
independent review of the complete intended three-file diff.

Falsifiers: changed solver outcome with tracing toggled, a traced sibling path
panic, the original regression missing/altered, altered expected output, or an
observer event attributed to a fabricated constructor. Any such result stops
the packet. No production semantic promotion is authorized.

## Baseline and exact leases

Branch `yulang3`, committed HEAD and upstream
`512c3b107c0942d390db5f6eab31b7891b38cb75`.

Writable lease: `crates/yu-solver/src/candidate_effect.rs`, baseline SHA-256
`75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909`.
The primary reopens this exact frozen owner lease for this revision only.

Read-only inputs: `crates/yu-solver/src/candidate_scheme.rs`, SHA-256
`bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`, and
`crates/yu-solver/src/shadow_apply.rs`, SHA-256
`c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`.
They remain part of the complete three-file review and any coherent checkpoint;
the implementer cannot edit them. The implementer also owns only
`tasks/agent-loop/inbox/effect-permission-rust-observer-repair-source.md` as
its frozen handoff.

Governing prior evidence: R1 incomplete outcome and independent review at
`tasks/agent-loop/history/effect-permission-identity-repair-20261028-r1-outcome.md`
and `tasks/agent-loop/inbox/effect-permission-identity-repair-review.md`.
Their Cargo receipt was 0/2 and their no-retry authority is exhausted. The
current independent review found a protected-fixture substitution and
observer-induced panic. No prior PASS receipt applies to the current bytes.

## Work and verification

Implementer: registered Luna/high lane, up to 900 seconds, exact writable paths
above. Audit adjacent test-observer `expect` assumptions, but do not broaden
the source edit beyond `candidate_effect.rs`.

Primary verification: one serial Cargo test invocation, one CPU, <=180 seconds,
<=2 GiB RSS, with the `shadow-apply-candidate` feature. Include the restored
nonrecursive regression, typed memo observation, and traced/untraced sibling
path case. Freeze final source/dependency and argv hashes before launch. Use one
uniquely named temporary target under the existing 16 GiB `/dev/shm` tmpfs,
with an 8 GiB artifact cap, offline and locked dependency resolution, and no
fallback to persistent storage. First verify write/execute access in the actual
execution context; if escalation is required, request it for that exact path.
Do not remount. On stop, timeout, resource pressure, unavailable dependencies,
or denied access, do not retry or fall back. After all descendants stop, retain
the compact result receipt and remove only the exact temporary target.

Fresh independent reviewer: compiler referee, up to 500 seconds, read-only.
Review the repaired source and complete intended three-file outbound diff,
including inherited hunks, protected regression, observer transparency,
feature-correct verification hashes and explicit non-claims. Reviewer does not
run builds/tests or Git operations.

Primary budget: 400 seconds for state synchronization, verification, review
adjudication, and primary-only Git. Total sprint budget 1,800 seconds; Astra 0.
Only the primary stages explicit intended paths, inspects every outbound
commit, and performs a non-forced push after review PASS. If the full intended
range is incoherent or any gate fails, keep it uncommitted and report the exact
blocker. All other dirty, quarantined, and untracked paths remain untouched.
