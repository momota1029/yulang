# Shadow capture of current SCC Q/R freshening identity

Date: 2026-10-07
Status: implemented opt-in shadow evidence capture; compiler-referee reviewed after minor test repair
Baseline: `7423c12ac1269049a9159b5bb4355f761991d19c`
Authority: user's default-off shadow/experimental implementation authorization; no semantic authority
Mode: M1, solver-local evidence plumbing

## Change

The `shadow-f5` path can now opt in to retaining successful current SCC
incoming-route freshening evidence and expose it through the SCC observer. The
ordinary `solve` entrypoint remains uncaptured. Retained data is limited to
current `DefinitionUseId`, target scheme identity, Q/R binder kind and
ordinal, opaque session-local fresh-row identity, and completeness. It does
not retain schemes, bounds, or a successor interface.

Capture distinguishes not requested, unavailable/incomplete, no closed
instantiation, and captured states, including a complete capture with zero
Q/R binders. Evidence is published only after the outer route succeeds;
failed or incomplete attempts do not become successful capture. The observer
joins exact SCC use and target scheme identities and rejects foreign capture
brands.

## Review and verification

An independent compiler referee found no blocking or major issue. One minor
test gap was repaired: repeated lookups now compare branded row identity, and
two successful uses of the same closed scheme check corresponding binder
identity and distinct per-use rows. Review covered current route/target joining,
state distinctions, coverage, rollback, non-retention of schemes/bounds,
ordinary uncaptured solve, and feature-off behavior. It did not certify
successor generalization, current-to-successor Q/R correspondence, source
`beta`/`Slots`, shared-contract transport, principality or production inference.

Focused verification passed in the isolated baseline worktree and was
repeated against the current worktree after integration:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 CARGO_TARGET_DIR=/tmp/yulang-qr-freshening-target \
  cargo test -p yu-solver --features shadow-f5,shadow-scc-observer --lib fresh_capture -- --test-threads=1
# 5 passed

RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 CARGO_TARGET_DIR=/tmp/yulang-qr-freshening-target \
  cargo test -p yu-solver --features shadow-f5,shadow-scc-observer --lib shadow_ -- --test-threads=1
# 31 passed

cargo check -p yu-solver
cargo check -p yu-solver --features shadow-f5
cargo check -p yu-solver --features shadow-f5,shadow-scc-observer
# all passed without warnings
```

After the test-only identity repair, the targeted capture test passed once
(474 filtered), and changed-file rustfmt passed. The exact test-only delta was
reviewed and checked in the isolated worktree. No broad workspace suite,
Oracle run or performance measurement was done.

## Remaining gates

This retains evidence from the current solver only. It does not construct a
successor generalized SCC interface, establish Q/R binder correspondence,
transport a shared call contract, or define `beta` / `Slots(beta)`. Recursive
soundness, principality, source adequacy and production cutover remain open.
