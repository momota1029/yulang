# F5b terminal-finish evidence boundary addendum

Status: Authoritative; implementation complete
Scope: terminal accounting-exhaustion test evidence only
Approved-by: user, 2026-09-22
Decision: do not add a cross-crate test API or feature solely to drive a
yu-types terminal-capacity seam from yu-solver
Drafted-by: primary from the discovered Cargo cfg(test) boundary
Reviewed-by: focused specification delta review, 2026-09-22
Supersedes: terminal-accounting exhaustion amendment §5 only at its combined
solver finalization/finish-exhaustion witness requirement

## Decision

Cargo builds yu-types as a normal dependency of yu-solver unit tests, so
yu-solver cannot invoke yu-types private cfg(test) terminal-capacity seams.
Reproducing a real usize aggregate overflow is not a finite test strategy.
This addendum does not authorize an exported test hook, a new Cargo feature, a
new production API, or an unrealistic allocation test.

The terminal evidence is split at the ownership boundary:

- yu-types proves the real terminal path: allocator-observed excess transitions
  to Exhausted before logical publication; finish returns IdentityExhausted; no
  arena, receipt, or checkpoint appears; unwind preserves the original panic.
- yu-solver proves its own existing error mapping and no-SolvedModule/no-final
  counter publication on finalization availability failure, and its production
  finish call maps the same ClosedTypeFinalizeError before SolvedModule and
  final ProductionCounters publication.

The solver does not need to reproduce the private yu-types overflow seam to
prove that its public error route has no partial publication. All ordinary
successful F4 route/projection/counter tests remain unchanged.

Return to design if this requires a shared test hook, a public feature/API, or
weakens yu-types real-terminal evidence.
