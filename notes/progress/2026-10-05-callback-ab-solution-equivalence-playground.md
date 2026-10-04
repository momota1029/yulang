# Callback A/B solution-equivalence playground

Date: 2026-10-05
Status: finite proof-search characterization; no compiler or semantic authority
Governing source: [callback context delivery](../design/2026-10-03-callback-context-delivery.md)
Experiment authority: [inference research playgrounds](../design/2026-10-04-inference-research-playgrounds.md)
Review: independent `spec_auditor` review clean; exact counts, minimum witness,
and stated limits match the model and governing contract.

## Conjecture and finite model

The bounded conjecture is that an A-style early step is a valid optimization
when it propagates only endpoint facts entailed by the completed B solution
relation, keeps the independently synthesized endpoints, and retains B's final
ordinary completed-interface query.

[`tools/research_callback_ab_solution_equivalence.py`](../../tools/research_callback_ab_solution_equivalence.py)
models three independently synthesized binary endpoint coordinates. It
exhausts every pair of body-constraint and completed-inequality relations over
the eight endpoint tuples: `256 × 256 = 65,536` pairs. For each pair it
projects the complete B solution relation to unary coordinate domains, applies
those domains early, and retains both original relations. The resulting A and
B solution sets are identical in all pairs; 58,975 have at least one solution.

The checker also shrinks an endpoint-copy mutation to one tuple. B admits
`(0,0,0)` while the expected endpoint is `(0,0,1)`; equating the synthesized
endpoints to the expected endpoint loses the B solution. This is a finite
illustration of the accepted rule that early propagation may not impose a
stronger equality than the final ordinary inequality.

## Boundary

The model is deliberately relational and tiny. It does not define Function
ports, Yulang's `A <: B` resolver, production constraint generation, callback
evidence, or an algorithm that can decide which propagated fact follows from B.
The exact-projection construction uses the B solution relation as an oracle,
so the result is a scheduling invariant characterization, not an optimizer
correctness proof. It establishes no callback adequacy or principal-scheme
theorem and changes no production path.

Focused verification passed:

- `python3 tools/research_callback_ab_solution_equivalence.py`
- `cargo --config 'build.rustc-wrapper=""' test -p yu-syntax research_lambda_header -- --nocapture`
- `rustfmt --edition 2024 --check crates/yu-syntax/src/tests/tails.rs`
- `git diff --check`
