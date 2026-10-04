# Callback A/B solution-equivalence playground

Date: 2026-10-05
Status: finite proof-search characterization; no compiler or semantic authority
Governing source: [callback context delivery](../design/2026-10-03-callback-context-delivery.md)
Experiment authority: [inference research playgrounds](../design/2026-10-04-inference-research-playgrounds.md)
Review: independent `spec_auditor` review found only a minor progress-record
omission on the tagged-witness delta. The record was synchronized and checked
by the primary agent.

## Conjecture and finite model

The bounded conjecture is that an A-style early step is a valid optimization
when it propagates only endpoint facts entailed by the completed B solution
relation, keeps the independently synthesized endpoints, and retains B's final
ordinary completed-interface query.

[`tools/research_callback_ab_solution_equivalence.py`](../../tools/research_callback_ab_solution_equivalence.py)
models three independently synthesized binary endpoint coordinates. It
exhausts every pair of body-constraint and completed-inequality relations over
the eight endpoint tuples: `256 × 256 = 65,536` pairs. Each B endpoint
solution retains four witness records `(method, adapter, residual, evidence)`;
the residual/evidence labels are correlated with method/adapter pairs and have
no production interpretation. For each relation pair, the checker projects
the complete B solution relation to unary endpoint domains, applies those
domains early, and retains both original relations. Tagged A and B solution
sets are identical in every pair; 58,975 endpoint pairs have at least one
solution.

A second loop samples 2,048 deterministic cases using seed `20261005`. It
selects body and inequality relations from the same 256-relation space and,
independently for each of the eight endpoint tuples, varies the available
subset of four tagged witnesses. This samples but does not exhaust the
tagged-relation family.

The checker also shrinks an endpoint-copy mutation to one tuple. B admits
`(0,0,0)` with all four method/adapter witnesses while the expected endpoint
is `(0,0,1)`; equating the synthesized endpoints to the expected endpoint
loses all four. A separate one-endpoint mutant that keeps only one witness
loses one of two alternatives differing in adapter, residual, and evidence.
These finite cases exercise both endpoint preservation and method/adapter/
residual/evidence choice preservation.

## Boundary

The model is deliberately relational and tiny. It does not define Function
ports, Yulang's `A <: B` resolver, production constraint generation, validity
of Yulang evidence, or an algorithm that can decide which propagated fact
follows from B.
The exact-projection construction uses the B solution relation as an oracle,
so the result is a scheduling invariant characterization, not an optimizer
correctness proof. It establishes no callback adequacy or principal-scheme
theorem and changes no production path.

Focused verification passed:

- `python3 tools/research_callback_ab_solution_equivalence.py`
- `python3 -m py_compile tools/research_callback_ab_solution_equivalence.py`
- `cargo --config 'build.rustc-wrapper=""' test -p yu-syntax research_lambda_header -- --nocapture`
- `rustfmt --edition 2024 --check crates/yu-syntax/src/tests/tails.rs`
- `git diff --check`
