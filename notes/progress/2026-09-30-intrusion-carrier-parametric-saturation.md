# Carrier-parametric saturation preservation

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Classification: conditional semantic theorem schema; no concrete carrier selected

## Theorem added

The abstract-semantics draft now defines assignments for the finite pure
saturation state and states a carrier-parametric preservation theorem. Under a
preorder whose endpoint interpretation validates the exact least/greatest,
join/meet, Function-decomposition, and irreducible-mismatch laws used by the
saturation rules, every finite stage reachable from initialized `S₀` has the
same satisfying-assignment fiber. An `X` mismatch at a reachable stage makes
that fiber empty. Variable references, including cycle back-edges, evaluate by
assignment lookup; the proof does not unfold them into recursive equations.

Independent compiler-referee review found no semantic issue in the stated
conditional theorem. It confirmed the proof obligations for retained Q
obligations, derived L/U bounds, transitivity, structural equivalences, and
reachable mismatch entries. An independent spec review found one minor scope
precision issue: arbitrary states could contain an invalid X marker. The text
now quantifies only over stages reachable from initialized `S₀`, where X is
populated solely by the mismatch rule. The spec review found no other issue.

## Limits and next proof obligation

This result is conditional: it does not construct a concrete carrier, prove
that any such carrier handles both recorded guarded recursive intervals,
relate source root projection to the semantic fiber, define scheme
instantiation/subsumption, or prove principality. In particular, the model
must preserve the distinction between an inequality cycle and an equation.
Gate C remains open, and no implementation authority follows.

`git diff --check` passed. No compiler code, Python, tests, or measurements
were added or run. Reviewer scope was limited to the saturation state/rules,
the theorem schema, and charter alignment.
