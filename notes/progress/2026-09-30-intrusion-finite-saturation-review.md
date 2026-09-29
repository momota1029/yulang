# Finite saturation presentation review

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Scope: order-free finite closure for the pure polarized fragment
Status: reviewed conditional lemma; no Oracle adequacy claim

## Candidate relation

The abstract-semantics draft now defines a finite saturation state
`(Q, L, U, X)`: subtype obligations, variable lower bounds, variable upper
bounds, and irreducible mismatch obligations. The rule operator is inflationary
and monotone over finite endpoint and obligation universes. Its least fixed
point is therefore finite and independent of processing order. Variable
back-references remain inequality endpoints; no rule unfolds them into
recursive equations.

Derived mismatches are explicit failures. After variable propagation,
trivial `Bottom`/`Top`, and structural decomposition, the pure fragment either
closes a matching atomic pair or records any other irreducible constructor
pair in `X`. This includes atom/Function pairs, incompatible Function shapes,
and nontrivial `Top`/`Bottom` comparisons. For an injective sort-preserving
renaming that fixes anchors, each saturation stage commutes with renaming;
the finite fixed-point relation and its mismatch set are preserved.

## Independent review

Independent compiler-referee and spec-auditor delta reviews first found that
the initial state had no failure outcome for `Int <: v <: String`. A second
review found that atom-only mismatch handling missed derived atom/Function and
nontrivial `Top`/`Bottom` cases. The state was extended with `X`, then its
mismatch predicate was broadened to all irreducible pure-fragment pairs. Both
reviewers confirmed closure of their findings and found no new issue in this
lemma's stated scope.

## Limits and next work

This remains a candidate abstraction of the recorded pure propagation rules.
It does not include evidence-sensitive edge selection, ordered diagnostics,
latent effects, tuples/records, nominal variance, recursive source schemes,
root/epoch preparation, scheme projection, or public normalization. It does
not yet prove that the frozen Oracle computes this closure from every source
context, and it does not establish soundness/principality for an interpretation
of endpoint variables. Those are still required for the full Oracle-capability
objective and before an implementation contract.

`git diff --check` passed. No code, tests, Python, or measurements were used or
changed.
