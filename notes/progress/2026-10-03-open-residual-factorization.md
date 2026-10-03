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

The conditional two-direction normalization-equivalence proof is in §4.1 of
the candidate and received a clean compiler-referee review. Its finite state
bound still assumes stable finite guard/evidence contexts. Operation-instance
§8 grounds inherited lexical context, identity-distinct sibling openings, and
invalidation/requeue behavior for a finite unsealed equality construction;
this does not establish coverage for every source-generated subtype check or
sealed lifecycle path.

## Follow-up: closed-regular Record field fiber

§7.2 of the candidate now extends the one-class Record fiber theorem from
identity-only atomic fields to fixed contractive regular field endpoints with
no unresolved flexible class. It characterizes all admissible label shapes
and leaves each selected field's joint lower/upper comparisons in an explicit
`F_f` fiber. The proof uses Record width/depth directly against one assembled
`X`; it never compares two endpoint successes through `X`. Recursive regular
field witnesses can be assembled by finite rooted-graph copies, while
permissions, original guards, and `Phi/K,D` remain conjoined on the same
assignment.

Independent bounded compiler-referee and spec-auditor reviews found no
findings in §7.2's fiber characterization or scope. This does not decide
field-fiber nonemptiness effectively, handle flexible endpoints/cross-field
constraints, or establish source-generation applicability. `git diff --check`
passed; no tests, builds, or measurements ran.

Next establish the source-wide context transition system while separating
immutable lexical identity from mutable dependency certification. Then
construct an effective joint representation for residual satisfiability plus
projection when unknown Record labels and recursive feedback vary. Uniform
scoped typing, effect/family compatibility, lifecycle, full acceptance,
termination/resource bounds and implementation remain open. The full goal is
active.
