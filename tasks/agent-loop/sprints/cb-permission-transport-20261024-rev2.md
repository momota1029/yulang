# CB-PERMISSION-TRANSPORT-20261024 — contract revision 2

Parent: revision 1,
`tasks/agent-loop/sprints/cb-permission-transport-20261024.md`, SHA-256
`e3d2e8bdffb4cfda48057525b5e7da076acb248eee2c0c5ddaf384b478b18cd9`.
This amendment preserves the parent claim, source semantics, baseline, exact
three runtime leases, total 3600-second sprint cap, quarantined reservations,
and review boundaries, except for the precise repair and one additional compile
check authorized below. No budget or elapsed-work reset occurs.

## Implementation review finding and bounded repair

The independent implementation review found a MAJOR at
`tools/inference-playground/src/runtime/machine.rs`: a pending callback
`Frame::ValueEntry` stores the original `entry_receiver`. If an argument
requests and the continuation captures that frame, replay may allocate a fresh
invocation owner while the copied executable frame still names the retired
owner. The current-owner check then rejects the entry before any callback
entry or receipt exists.

Repair only the dormant executable `ValueEntry` owner during
`TemplateNode::Bind` replay, resolving it through the existing per-replay
control map and `resolve_control` discipline before pushing that frame. Do not
rewrite any already-created callback entry, use, receipt, observation or
captured view. Record this as a distinction between executable pending-entry
ownership and historical evidence ownership. No source semantics, schema,
grant condition, owner path or authority outside the three existing runtime
files changes.

The original frozen implementation review is recorded as **MAJOR; not
accepted**. After the bounded repair, freeze replacement hashes for all three
runtime files and obtain an independent delta review of owner remapping,
borrowed-live-owner replay, fresh-owner replay, and unchanged historical
receiving identities. Acceptance still requires that review.

## One additional verification command

Revision 1's sole authorized Cargo check has already run against the prior
bytes. After the repaired three-file diff passes independent delta review,
Luna may run exactly one additional
`cargo check -p yu-hir -p yu-solver -p yu-playground` against the repaired
bytes. This is the only additional build authorization in this sprint. No
tests, expected-output changes, runtime probes or other compiler commands are
authorized. The check is compile evidence only and cannot establish runtime
behavior or proof closure.

All other revision 1 terms remain in force. Keep
`SOURCE-SAFETY-BRIDGE`, the original Simple-sub A/B claims and broader source /
native coverage open.
