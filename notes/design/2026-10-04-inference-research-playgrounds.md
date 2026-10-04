# Executable research playgrounds for inference proof search

Date: 2026-10-04
Status: Authoritative user direction; research implementation permitted
Scope: executable models for open SCC-intrusion inference obligations
Approved-by: user, explicit direction on 2026-10-04
Implementation authority: isolated research playgrounds; no production inference routing
Supersedes: none

## Direction

The user authorizes executable experiments before complete proofs. Proof
search for open inference obligations should use the loop

```text
conjecture -> implement/check -> break -> shrink -> revise conjecture -> prove
```

Research models may assert conjectured lemmas and invariants, enumerate finite
models, generate randomized cases, and minimize counterexamples. A failed
model may be discarded after its useful obstruction is recorded. A passing
bounded search is characterization evidence and never substitutes for a
theorem.

This direction particularly applies to:

1. structural finite-model property, including shifted open-descriptor
   equations and the reviewed complete `Gamma_P^coh` / conflict-rank account;
2. callback production bridge and finite source-generated endpoint rules;
3. principality and the representative source programs already recorded in
   the acceptance criteria.

Prefer small isolated programs and checkers. Encode conjectures as executable
assertions, search for counterexamples, and shrink any failure before revising
the conjecture. Existing reviewed proof packages and counterexamples remain
governing inputs; a playground must state exactly which fragment it models
and must not turn an omitted rule into an implicit premise.

## Boundaries

- Production compiler replacement is not authorized by this direction.
- No soundness, principality, callback adequacy, or unrestricted FMP claim
  follows from a finite search.
- Do not add a new durable semantic rule merely because a playground passes.
  A new language decision still requires explicit user approval and the normal
  authority/review process.
- An experimental model may be rewritten or removed when a counterexample
  invalidates its design. Preserve the minimized obstruction and the reason
  for abandoning the model in a progress record.
- Keep playground verification focused and bounded; report search dimensions,
  generation counts, shrink results, and unsearched space.

## Current work order

The finite parent/use transport test model is a completed narrow experiment.
The next active playground targets unrestricted structural FMP directly: it
must model exact descriptor shifts and the complete finite-quotient coherence
rules from [finite feedback quotients](2026-10-04-structural-finite-feedback-quotients.md),
and search for either escaping first-conflict ranks or a boundedness invariant.
Do not substitute the two-sided preclosed witness checker for this open gate.
Callback bridge and principality models remain active subsequent lanes.

This order selects research activity only. It does not assert a theorem,
introduce a new carrier/relation, or authorize production cutover.
