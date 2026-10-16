# Catch Apply / CandidateSourceCall bijection run receipt

Sprint: `catch-matcher-introduction-and-call-bijection-20261017`, contract rev6
SHA-256 `aa97e843eb1e73dd61772184d83dbe60a937d5321b378b290b7dc4b37fb94bdb`.

## Frozen inputs

- Example `crates/yu-solver/examples/research_catch_source_export.rs` SHA-256
  `4ae13f891655a8afebc25890d10cf512c4dd7365436f9f3cd24380f22e20e50e`.
- Original implementation handoff
  `tasks/agent-loop/inbox/20261017-catch-call-bijection.md` SHA-256
  `9b248430f64478d4be3624d3b4769f187c6b89f6e9312c57eccb0e3bc90d7b54`.
- Carrier repair handoff
  `tasks/agent-loop/inbox/20261017-catch-call-carrier-repair.md` SHA-256
  `5c1e02bedff31eb3bfa43569104bcfe02e6c1dd8b2a118de16e72ba2adc8a975`.
- Pre-carrier-repair snapshot
  `tasks/agent-loop/snapshots/20261017-catch-call-bijection-pre-carrier-repair.rs`
  SHA-256 `dfb67257941f628faa2c3c9f31504cedb5c53d8f12e25e08466ff3f8a71f933f`.
- Proof artifact and handoff remain pinned at `ea0b96693114f9cbe9c8e6306b4dcff6fd522baef2c9076277de1a33801a2936` and `1e955d4bd3aa33a616370763cb98b42a0d5201306b66d9ca7680e3ae9fa5d933` respectively.

The rev6 source received a fresh CLEAN independent pre-run review after the
rev3 inventory omission was repaired. The reviewer verified all 70 direct
contract pins. No source bytes changed after that review.

## Sole command and result

Luna invoked exactly once:

```text
timeout 120s env CARGO_BUILD_JOBS=1 cargo run -p yu-solver --features shadow-apply-candidate --example research_catch_source_export
```

Exit code: **0**. Tool-reported wall time: **1.188 seconds**. Cargo reported
`Finished dev profile` in 1.27s, then executed the example. No retry or second
invocation occurred. Cargo emitted one warning: unused local `owner` at example
line 300. It did not affect the completed run. No tests or separate build were
run.

## Observations

- Source literal remained 138 bytes; parse structural recoveries were empty.
- The required HIR errors were present and guarded:
  - `UnsupportedItem`, bytes `0..44` (`act signal`).
  - `UnsupportedExpression`, bytes `75..138` (Catch binding).
- Complete supported-LocalSource inventory found **3 authentic Apply** sites.
- Ordinary `CandidateInference::solve` observed the same HIR and returned zero
  candidate conflicts.
- All **3 CandidateSourceCall** records matched exactly one Apply. Each had
  exact owner/source/callee/argument identities and keys; checking occurrence
  matched the Apply, and cause referenced its checking occurrence.
  Per-Apply counts: `[1, 1, 1]`.
- `fresh_use` returned the exact `id` occurrence; borrowed exports returned
  `id` (10 nodes, 4 rows) and `result` (3 nodes, 1 row).

## Boundary and remaining obligations

These are observations on the returned partial HIR and candidate object only.
The two unsupported HIR errors remain. The run establishes no accepted source,
complete source representation, source typing, handler adequacy, detached
export, runtime semantics, or parent theorem closure. `CATCH-EXIT-INPUT-1`, F1,
FK1 and every downstream parent remain OPEN. The proof packet's CLEAN review
still locates the first missing definition at typed formation of the original
outside `MatchRequest_H` input at actual `C_out`; packaging and Apply/source-call
bijection do not discharge it.

Fresh independent post-run receipt review is pending. The consumed Cargo cap is
one of one; this command must not be repeated.
