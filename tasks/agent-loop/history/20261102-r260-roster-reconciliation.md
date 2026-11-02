# R260 roster reconciliation — 2026-11-02

Primary-owned runtime reconciliation only. This record does not certify the
R260 proof candidate, stop its writer, release its reservation, or release its
path leases.

At 2026-11-02 08:34:59 UTC, `collaboration.list_agents` showed `/root` running
and the completed `next_action_selector`; it did not show
`/root/sol_r260_replay_ack_order`. A direct `send_message` to that identity
failed because the live agent could not be found. No cessation receipt was
available, so the worker remains UNKNOWN and both exact output paths remain
quarantined.

The R260 theory output appeared during reconciliation and was not stable:
the selector observed SHA-256
`4180c786934d096a1d350dcacbaf2e3f0d53f82d3d682332a2a3fe1bbac85d69`; a later
primary read observed `87455f756a26d7d4cab0368be3e3b67741c7afe70d958407cc3de2cde90a1aca`.
The file labels itself an unreviewed candidate and claims checkpoint
`6263619b003535528ac229e3f052e40f1d754312`; these are unauthenticated draft
claims, not a frozen handoff or writer-stop evidence. The R260 inbox handoff
and named admission record were absent at inspection. The theory bytes were
not reviewed or edited.

The active sprint is RECONCILE. Preserve the full 2,400-second R260 assignment
reservation. Keep the original contract and source pins; do not reassign either
path, review a moving target, mark STOPPED/DONE, or count the candidate as
progress on the original parent. The separately reviewed R249/R250 evidence
and R70 open premises retain their existing statuses.

## Required recovery evidence

Resume R260 only after supported runtime evidence identifies the writer and
provides a frozen theory file and handoff with final hashes, source-pin
verification, budget use, parent application, exact remaining R70 premises,
and write-stop evidence. Otherwise preserve the quarantines and choose only a
versioned, disjoint assignment after fresh baseline and dependency
authentication.
