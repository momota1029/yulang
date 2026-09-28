# F5c FlatDraft owner carrier and same-ID transfer checkpoint

Status: the verified core carrier and staged-transfer slice is checkpointed.
The remaining family-6 event-owner coverage, the all-family event fold, the
fresh preflight, and the §26/§34 scale matrix remain open.

Authority: the approved flat-indexed staged-candidate design and the
Authoritative no-numeric-resource-cap addendum. This is measurement-only,
feature-gated ownership evidence; production continues to use the boxed path.

## Included diff units

- `crates/yu-solver/Cargo.toml` and `crates/yu-types/Cargo.toml`: declare the
  opt-in probe feature and its forwarding boundary.
- `crates/yu-solver/src/f5c_draft.rs`: the six-vector `FlatDraft` owner
  carrier, actual capacity/requested-length observations at its direct
  mutation methods, and focused identity/transfer lifecycle witnesses.
- `crates/yu-solver/src/f5c_draft_heap.rs`: ordered sidecar primitives,
  feature-gated physical-owner identities, checked six-buffer transfer
  preflight, unchanged-ID transfer into staged buffer owners, and release
  tracking for the resulting allocation tokens.
- `crates/yu-solver/src/f5c_generalization.rs`: staged-length snapshot and
  transfer helper, owner attachment when the raw flat draft is created, and
  the candidate staging call sites that use the transfer helper.

The checkpoint does not claim complete family-6 coverage. Later direct-owner
hooks in replay/materialization/sink/normalization, the lane-55/56 occurrence
shape and probe-meter repairs, source-peak synchronization, the streaming
checker, the remaining seven resource families, and all measurement runs are
outside this diff.

## Review and verification

The selected M2 slice had independent specification and performance review;
both reported no blocking or major findings. For this checkpoint, checks ran
against an isolated worktree formed from HEAD plus only the listed staged
diff:

- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --offline -j 2`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe --offline -j 2`
- `RUSTC_WRAPPER= cargo test -p yu-solver --lib --features f5c_resource_probe --offline -j 2 flat_draft_ -- --test-threads=1` (3 passed)
- staged `git diff --check`

The focused witnesses cover moving a draft, failed atomic preflight followed
by release, and reusing the same owner IDs across staged transfer and final
drop. No broad suite, matrix preflight, benchmark, or scale process ran for
this checkpoint; measurement budget consumed: zero.
