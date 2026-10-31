# R87 terminal lease compaction

R87 is closed under the linked outcome. These five terminal R87 path rows are removed from `current.json` to make room for the live R88 state. No artifact or workspace path was deleted. R80/R81 unknown-owner frozen leases remain in current state.

Outcome: `tasks/agent-loop/history/native-drain-reader-correspondence-20261031-r87-outcome.md` (sha256 `72e2fc795a8d7e10c104ad2fc902f884165d1355dccb37476da264267c582816`).

## Compacted exact rows

- `tasks/agent-loop/sprints/native-drain-reader-correspondence-20261031-r87.md` — owner `/root`, state `HELD`, recorded sha256 `fb57b17b311afb459dd3aea20819ae902955651862c4e401729189dc3e0a5314`.
- `notes/theory/lean/YulangClosure/NativeDrainReaderCorrespondenceR87.lean` — owner `/root/r86_proof`, state `FROZEN`, recorded sha256 `1ac359eba68583441808be1e55c110071a3bd207b567adfe73381c35366148e8`.
- `tasks/agent-loop/inbox/effect-permission-native-drain-reader-r87-proof.md` — owner `/root/r86_proof`, state `FROZEN`, recorded sha256 `ef2a0a2e157301fe7a322fd2c395b9935154a6d16bcc9a7f483270d1991a72b1`.
- `tasks/agent-loop/inbox/effect-permission-native-drain-reader-r87-source.md` — owner `/root/r86_source`, state `FROZEN`, recorded sha256 `3e911c32e76931cf8ff38d0a97de2a8eb711c3a3aac5e45e7bf7cd2951fae3d8`.
- `tasks/agent-loop/inbox/effect-permission-native-drain-reader-r87-review.md` — owner `/root`, state `FROZEN`, recorded sha256 `39d301c99e4b906a73a20cb20a727ceca4cf8a58102cd66178223af4597403b8`.

This receipt archives the exact current-state lease records; it makes no claim that working-tree bytes were revalidated. The pre-existing byte-identical duplicate lease for `crates/yu-solver/src/candidate_receiver.rs` was deduplicated without changing its owner, state, or hash. The existing R88 Lean candidate lease was transitioned from HELD to FROZEN with the handoff-pinned hash. Only resolved R87 leases were compacted. Active and UNKNOWN leases, unresolved paths, pending questions, and the R88 contract/manifest/admission/results remain represented.
