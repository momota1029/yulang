# R269 stop-receipt hash reconciliation — 2026-11-02

At HEAD `56be5b6e31c3b7d77b8d720f71a02a41b571034e`, the committed
`20261102-r269-read-authority-stop.md` hashes to
`ad091c212628a4cb6ff1693ae7cabc6a2288ae118bbfef239d6597c0d8caa9b6`.
The compact state's frozen lease and the prepared, unadmitted R269-r2 packet
instead cite `9e28cdc0d90509981765dccb60fa7d9a791fb38f1325a71dcd9d6dca4d4c7148`.
This primary observed that earlier hash in the shared state before the stop
record was committed. Its exact bytes have not been recovered. Do not represent
the two hashes as the same immutable revision.

The committed record reports the R269-r1 producer's explicit cessation, no
technical or output reads or writes, no descendants, and a full 1,200-second
charge. The user subsequently stated that they had no work running; this does not
identify the owner or prove cessation of any other session or children. The identity is absent from this primary's live roster; that
absence alone does not authenticate cessation. Preserve the committed record
and R269-r2 bytes unchanged. R269-r2 is superseded before admission because its
stop-receipt pin is stale. No proof result, production authority, budget refund,
or release of any UNKNOWN writer's paths follows from this reconciliation.

At the time of observation, the compact-state frozen lease recorded the earlier
hash; its disposition required primary-owned reconciliation. The earlier recorded hash is retained above as
provenance. A subsequent fresh contract must pin a reconciliation and the actual
stop-record hash.
