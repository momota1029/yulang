# R281 source-boundary review — INCOMPLETE/BLOCKING

Reviewer `/root/r281_source_boundary_review`, coordination session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`; requested compiler_referee,
Sol/medium; observed model/effort UNKNOWN. Full 300-second reservation charged.
All technical reads stopped; no writes, descendants, tests, builds, Cargo,
Lean, probes or Git.

Frozen review target: contract
`tasks/agent-loop/sprints/extrusion-entry-validity-r281.md`
(`4b737c39cb35cd9de013b053eeee4397e48e4f770fa64500969d66b0f658477f`),
view/ranges/exclusions/index hashes as recorded in
`tasks/agent-loop/history/20261103-r281-source-boundary-review-go.md`
(`f50b4d45c1b7fe6c488f131947ccc09eb63bfcdd6862f570570ba174b463129c`).

## Integrity and process disclosure

All 36 R255 path/hash rows, seven source pins used by the view, 134 indexed
payloads, and 96 exclusion hashes/disjointness checks matched. This proves the
listed byte correspondence only; it does not establish complete cfg boundaries
or source-owner coverage. After GO, the reviewer displayed the first 12 view
lines before independent source-pin verification; all later pin checks matched.
No unindexed source bodies were opened. The order is disclosed; the review
remains limited to the exact admitted view and intervals.

## Blocking omitted owners

- Restoration: `candidate_extrusion.rs:962–963` (R281-R0027) calls omitted
  `candidate_begin_bound_restoration` and `candidate_drive_bound_restoration`.
  `candidate_scheme.rs:4516–4517` (R281-R0031) calls omitted
  `begin_candidate_fresh_bound` and the same driver. Actual restored-bound
  writes and failures are therefore not covered.
- Source construction/driving: `candidate_source.rs:2359/2362` (R281-R0016)
  calls omitted `begin_candidate_source` and `drive_candidate_source`.
  `lib.rs:10126` starts with `candidate_graph: None`; no indexed payload
  constructs its `Some` state or initializes/extends representative forests.
- Transaction/extrusion ownership: omitted direct owners are
  `begin_route_transaction_for` at `lib.rs:14533` (R0011), `rollback_workspace`
  at `lib.rs:10047` (R0005), `begin_candidate_extrusion`,
  `retain_extrusion_parent`, and `finish_candidate_extrusion` at
  `candidate_extrusion.rs:30/135/581` (R0022), `candidate_replay_bound` at
  `candidate_extrusion.rs:586` and `candidate_intrusion.rs:704`, and
  `candidate_reopen_root` at `candidate_intrusion.rs:698`.

These omissions violate R281's complete constructor/write/restoration/
rollback/resume and direct-helper contract. The reviewer recommends adding the
exact authenticated production owner bodies and necessary dependencies, then
obtaining a fresh boundary review. No R281 Sol owner gate or proof stage is
issued. Parent/A/B remains 0->0; R70 stays OPEN; `NO_SAFE_CODE_SLICE`.
