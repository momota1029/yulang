# Independent review: formal permission projection r4

Verdict: accept as qualified, incomplete static source evidence. No blocking,
major or minor findings. No successful permission-projection counterexample or
unconditional r2-B theorem was established. Endpoint-image, parent theorem,
native and production gates remain OPEN.

## Accepted result and exact boundary

The reviewer independently checked the local checkpoint/publication/rollback
owners, visible session transaction delegation, capture/export lookup, relevant
embedded tests, governing policy and frozen r2/r3 evidence.

`candidate_effect.rs:313–342` checkpoints permission length/accounting, journals
new domain keys, removes those keys during rollback and truncates permissions.
The handoff correctly makes the cleanup conclusion conditional on the correct
outer checkpoint and complete insertion journaling. Publication rejects an
existing domain key and associates the new negative term with the appended
permission records (`:1638, :1687–1691`). The body leaves journaling conditional
on an active outer undo.

`lib.rs:9424, 9514–9533, 9678–9681` shows session transaction setup, successful
commit and failed-route delegation. It does not establish that the consumed
intrusion undo contains the same state's pre-publication effect-algebra
checkpoint or restores the associated row/term epoch.

The exact next source dependency is
`crates/yu-solver/src/candidate_intrusion.rs`, specifically
`State::begin`, `Undo::effect_algebra` and `State::rollback`. Its bytes remain
UNKNOWN because neither producer nor reviewer opened it. Admitting that owner
can establish or refute the first missing checkpoint equation; it alone does
not automatically close all B. Older associations, candidate-state/capture
replacement, C (canonicalization/store association) and D (successful
capture/export) remain separate.

## Authentication and execution

- r4 handoff SHA-256: `92fc0eb406ad0b7b82801ed86c33723bdc9483aee997421563dac2d12154d8a7`
- r4 contract SHA-256: `d158c2e14e44d6f6c5bc3e76af7a1ec94cf24c090ba266de9ad93ce958b0b1cc`
- All seven source-owner pins and five frozen r2/r3 input hashes matched.

Reviewer: `/root/formal_permission_projection_r4_review`, fresh non-author
`compiler_referee`; STOP after read-only review. No tests, builds, probes, Git,
network, writes or descendants. Embedded tests were not executed. No claim of
Lean verification or production permission follows.
