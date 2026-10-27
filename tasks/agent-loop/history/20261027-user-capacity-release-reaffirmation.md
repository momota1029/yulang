# User-directed capacity release reaffirmation

Date: 2026-10-27
Authority: explicit current-user instruction to release the reservations referred
to in `current.json`, amend the rule and synchronize with active agents.

## Live-roster synchronization

The live collaboration roster was inspected before applying the instruction.
`/root` was RUNNING; every listed child agent was `completed`. No non-primary
agent was RUNNING or WAITING, so no child notification or cessation wait was
needed.

## Capacity disposition

The full UNKNOWN-assignment set was unambiguously targeted by the instruction.
Its nine non-primary capacity reservations were already released under the
earlier receipt `tasks/agent-loop/history/20261027-user-capacity-release.md`
(SHA-256 `7d30faa71449af50c50539307b3a11d062735b64d522eac93656467ff94968a8`).
This reaffirmation is idempotent: it releases no additional slots and records
no worker as stopped. The same nine observations remain UNKNOWN, and their exact
paths remain quarantined.

The exact IDs are those listed in the prior receipt and in
`current.json`'s `legacy_reconciliation.reservations` and `workers` rows.

## Rule update

The sprint rules now permit a clear user directive to target either named
UNKNOWN assignments or the complete UNKNOWN-assignment set in `current.json`.
Live-roster synchronization, notification of affected RUNNING/WAITING children,
UNKNOWN observations and quarantined paths remain required.
