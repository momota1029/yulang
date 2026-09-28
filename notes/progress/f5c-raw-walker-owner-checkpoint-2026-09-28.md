# F5c raw walker owner event foundation checkpoint

Status: the feature-gated raw-owner lifecycle primitive is independently
reviewed and verified. Its family-specific lane call sites remain open.

Authority: the existing F5c physical-event observation contract in the
no-cap scale measurement plan and the Authoritative no-numeric-resource-cap
addendum. This adds no compiler input or work limit and does not change
production behavior.

## Included diff unit

- `crates/yu-solver/src/f5c_draft_heap.rs`: `RawWalkerOwner` creation,
  capacity/requested-length observations, and release; same-ID adoption into a
  tracked raw vector; suppression of the raw release after successful
  transfer; single release on failed adoption; and requested-length updates
  for tracked-vector mutation methods.

This checkpoint establishes the reusable owner lifecycle only. Lane 55/56
occurrence wiring, the other family-6 lanes, all-family event folding, the
fresh preflight, and scale measurements remain open.

## Review and verification

Selected M1 with one independent `spec_auditor` delta review. No blocking,
major, or minor finding remained. Checks ran in an isolated worktree formed
from the branch HEAD plus only this staged diff:

- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --offline -j 2`
- `RUSTC_WRAPPER= cargo test -p yu-solver --lib --features f5c_resource_probe --offline -j 2 raw_walker_owner_ -- --test-threads=1` (2 passed)
- staged `git diff --check`

No broad suite, matrix preflight, benchmark, or scale process ran; measurement
budget consumed: zero.
