# Catch Apply / CandidateSourceCall post-run receipt review

Sprint: `catch-bijection-postrun-receipt-review-20261017`, contract rev1
SHA-256 `19313d4be86766f4600b6513bee6e347d8c1e00e6f9a46ee331ab5a23c9ba59e`.

Reviewer: `/root/catch_bijection_postrun_review`, fresh
`regression_auditor`, requested Sol/medium, observed model/effort UNKNOWN.
Reviewer STOPPED; no files changed, no descendants, no rerun, no build, test,
Cargo, probe or Git operation. Full 90 seconds charged conservatively.

## Disposition

**CLEAN for bounded receipt consistency review.**

- All 11 direct dependency/contract hashes matched, including the frozen receipt,
  corrected example, both implementation handoffs, pre-repair snapshot, proof
  artifacts and prior contracts.
- The corrected example unions supported expression carriers with opt-in
  binding LocalSources via authentic HIR definition roots, checks ownership,
  and deduplicates roots by source-object identity.
- It requires exactly one `CandidateSourceCall` per Apply across retained
  supported LocalSources, with matching owner, source/callee/argument objects
  and keys, checking-occurrence agreement, cause consistency, equal totals and
  per-Apply counts `[1, 1, 1]`. This supports the receipt's stated **3/3
  correspondence within retained supported LocalSources**.
- Both `UnsupportedItem` and `UnsupportedExpression` kinds are required and
  printed. Exact byte spans are recorded runtime observations; the example
  guards the diagnostic kinds, not exact spans.
- Receipt command, attempt 1/cap 1, exit 0, timing, warning and no-retry claim
  agree with the pinned contract's `execution_result`. Invocation history is
  Luna's reported evidence; no independent execution transcript was supplied.
- The receipt correctly limits all observations to partial HIR and leaves
  source acceptance, complete typing, handler adequacy, detached export,
  runtime semantics, `CATCH-EXIT-INPUT-1`, F1/FK1 and downstream parents open.
  Checking/cause consistency does not establish an independently expected
  private constraint slot or cause identity.

This is a bounded consistency review, not independent authentication of the
compiler process or a theorem proof. No source changed after the run. The sole
Cargo invocation remains consumed; no retry is allowed.
