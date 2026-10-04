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

**Mathematical status update:** the subsequently reviewed
[finite-fence theorem](2026-10-04-structural-fmp-fence-completion.md)
proves normalized pure structural FMP and BR. The structural proof-search
order recorded below preceded that result; arbitrary-package playgrounds
remain useful for checking constructions, but are no longer a missing
premise for the pure FMP theorem. This update changes no experimental or
production authority. Callback bridge and principality remain open lanes.

The finite parent/use transport test model is a completed narrow experiment.
The first structural playground now exercises the complete restricted
`Fbar/G` rules on `q = Function(x, Int), x <: q`, sweeps cutoff quotients, and
enumerates all labelled two-generated monoids through size four. A second
checker, `tools/research_gamma_quotients.py`, generates 495 packages in the
restricted one-Function-root / one-Int-root / one-free-root fragment, each
with zero to two independently identified bounds, and checks all 449 such
monoids. It compares ranks against the first checker on their shared package
and independently validates every surviving finite graph. Exact scope and
observations are in the
[structural FMP progress record](../progress/2026-10-04-structural-fmp-feedback-rank.md#generated-package-quotient-search-2026-10-04).
The next structural step is to generalize the package language itself to
arbitrary normalized `Gamma_P^coh`, including exact shifted descriptors and
full domain/head/child coherence, then search and shrink candidate failures.
Do not substitute the two-sided preclosed witness checker for this open gate.
Callback bridge and principality models remain active subsequent lanes.

This order selects research activity only. It does not assert a theorem,
introduce a new carrier/relation, or authorize production cutover.

### Callback and principality characterization models

[`tools/research_callback_lift.py`](../../tools/research_callback_lift.py)
checks the local old-tuple-preserving total-coordinate extension shape from
Theorem C §2.6 and minimizes a two-row obstruction to replacing linked source
witnesses with independent marginals. Its flat one-fiber model does not test
general constructor transport, source realization, or Theorem C's full
inclusion. A finite `bind`-shaped relation join additionally checks that a
shared intermediate coordinate, fiber, owner pair, scope, receipts, and port
evidence survive total lifting across a composed relation; it remains a
relational toy, not the operational bind/resumption semantics.
[`tools/research_principal_support.py`](../../tools/research_principal_support.py)
checks finite common-support factorization while retaining separate
occurrence endpoints. This is only powerset-level evidence; it is not an
effect comparison or principal-scheme theorem. Exact dimensions, minimized
obstruction, and remaining proof gates are recorded in the
[callback/principal playground report](../progress/2026-10-04-callback-principal-playgrounds.md).
[`tools/research_callback_entry.py`](../../tools/research_callback_entry.py)
checks the selected Value-entry source order and finite bind/resumption paths;
it does not model typed endpoint denotation or multi-shot owner semantics.
