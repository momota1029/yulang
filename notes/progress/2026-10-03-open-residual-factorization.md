# Open residual factorization candidate (2026-10-03)

## Objective and authority

Continued the full SCC-intrusion type-inference replacement objective at
Milestone 3. The immediate gate is the next theorem named by
`notes/design/2026-10-03-scoped-constraint-solving.md` §7: principal residual
factorization for open flexible heads and Record extensions, with scoped
permissions, projection summaries and original joint constraints retained.
The redesign charter and current task explicitly grant no compiler
implementation authority.

## Candidate produced

`notes/design/2026-10-03-open-residual-factorization.md` proposes a finite
normalizer over descriptor-known pairs after the rational equality quotient.
It keeps any comparison with an unresolved flexible head as a residual edge,
so `X <: {}` covers all finite Record extensions without selecting a row
skeleton. Equality aliases share one quotient assignment; permissions,
original `Eq`, invariant coordinates, witness identity and joint `K,D/Phi`
remain correlated. Projection summaries are derived from the whole assignment
and are not independent ports.

The candidate distinguishes scope-guard failure, structural failure after an
admitted guard, and successful normalization. A successful residual graph is
the premise of the proposed factorization equation. This repairs the empty
residual-graph counterexample for a known mismatch such as `Int <: Bool`;
scope failure remains a separate outcome under charter §22.

## Review and evidence

M3 used one architect to derive the bounded theorem shape, then independent
compiler-referee and spec-auditor reviews. The initial reviews found one major
omitted structural-failure outcome and one minor missing matching-atom case.
Both were repaired. A fresh compiler-referee delta review of §§3–4 found no
remaining findings. The source design and theorem authorities were checked
against the affected charters and predecessor packages.

No compiler code changed. No tests, builds, or measurements ran. Review does
not prove the proposed factorization theorem or any open-bound decision
procedure.

## Remaining gate

First formalize and prove normalization equivalence and the conditional
factorization, including recursive pair feedback, variance, invariant mutual
comparisons, alias identities and permitted-name propagation. Then construct
an effective joint representation for residual satisfiability plus projection
when unknown Record labels and recursive feedback vary. Source generation,
uniform scoped typing, effect/family compatibility, lifecycle, full
acceptance, termination/resource bounds and implementation remain open. The
full goal is active.
