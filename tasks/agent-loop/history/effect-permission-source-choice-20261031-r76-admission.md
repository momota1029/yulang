# R76 admission — exact-use formal-owner choice

Sprint: `EFFECT-PERMISSION-SOURCE-CHOICE/20261031-R76`

Status: ADMITTED. The primary admits the frozen contract and R1 input manifest under the continuing `research/simple-sub-intrusion` authority.

- Baseline: `9b523f587cf1e8cf2142ede750fa85121876d415` (`yulang3`).
- Contract SHA-256: `87325ab223af0e98a6ca8c78162ead6ba1d72403b318342d155ee5dd55069936`.
- Input manifest SHA-256: `33a8769ab21ded37b85e436b90fe67f12ab8561eb2ffd0e90fe754acc23bb0dd`.
- Rust writer `/root/r76_rust`: `candidate_receiver.rs` and its assigned handoff only; 1000 seconds.
- Lean writer `/root/r76_proof`: `SourceInternalChoiceR76.lean` and its assigned handoff only; 2600 seconds; no more than two pre-frozen direct stdin audits.
- Fresh reviewer `/root/r76_review`: assigned review handoff only; starts after both writers STOP / WRITES STOPPED; 1200 seconds.
- Primary closeout budget: 1200 seconds including at least 500 seconds for review, reconciliation, archive, commit and push. Astra: 0.

The source constructor, Lean target, falsifiers, exact leases, dependency pins, audit bounds, prohibited generated outputs and closure limits are fixed by the contract. `lib.rs`, R39/R45/R49/R55/R57/R62/R63/R47/R65/R66 and R75 dependencies are read-only pins. No test, compiler, Cargo, Lake, project build, environment, worktree, cache, target or scratch output is authorized. All 32 pending items and existing UNKNOWN/quarantined paths remain unchanged.
