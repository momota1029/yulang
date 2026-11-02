# R263 stop and roster reconciliation — 2026-11-02

The earlier live-roster reconciliation (`20261102-r263-live-roster-reconciliation.md`)
recorded `/root/sol_r263_source_causal_episode` absent from that primary's roster
and correctly quarantined both R263 output paths. In this primary's actual live
roster, the exact identity was present as RUNNING. Luna notified it to stop
because compact state was UNKNOWN and the leases were QUARANTINED. The worker
acknowledged STOP and reported:

- It wrote only `notes/theory/2026-11-02-source-causal-episode-r263.md` before
  STOP. After interruption, Luna inventoried 12,660 bytes at SHA-256
  `99ec81fd39aad2d04ecac66c1474ec51edb7e913c4daeb162f4b6a61c92bfaac`.
- It did not write `tasks/agent-loop/inbox/source-causal-episode-r263.md`.
- It created no descendants and performed no Git, source edits, scratch,
  tests, builds or probes.
- Its pre-source gate had matched all 36 R255 pins and the contract/admission
  hashes. No freeze check or handoff was completed.

Luna then interrupted the exact live identity; the interruption tool returned
previous status RUNNING. This is cessation evidence for this roster/session,
not evidence that the other primary's roster was incorrect. Keep both exact
output leases QUARANTINED pending byte/hash inventory and primary adjudication.
The theory file is provisional, unreviewed and not accepted as a proof result.
The inbox remains absent/unwritten. No source or Rust lease is involved.

R263 remains STALE. No replacement writer is admitted. The 2,400-second
assignment reservation remains held until capacity accounting is reconciled.
