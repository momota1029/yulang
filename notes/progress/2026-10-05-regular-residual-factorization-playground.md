# Recursive regular residual factorization playground

Date: 2026-10-05
Status: Bounded pure-structural characterization; no solver or semantic authority
Governing sources: [scoped constraint solving](../design/2026-10-03-scoped-constraint-solving.md) §3; [open residual factorization](../design/2026-10-03-open-residual-factorization.md) §§2–4; [research playground direction](../design/2026-10-04-inference-research-playgrounds.md)
Review: compiler_referee found no remaining findings in the graph-copying, fixed-point, residual-normalization, and count scope after the initial model defects were repaired.

## Experiment

[`tools/research_regular_residual_factorization.py`](../../tools/research_regular_residual_factorization.py)
compares direct greatest-fixed-point structural subtyping on instantiated
regular graphs with finite normalization that retains variable-headed pairs
as residual inequalities. Functions use contravariant arguments and covariant
results; Records are mandatory-width records over labels `a,b`.

The exhaustive part uses a selected 15-node shallow endpoint graph and checks
all 225 ordered endpoint pairs under all 144 pairs of closed assignments from
a 12-graph finite assignment set: 32,400 differential checks, covering 8,064
residual instances and 39,600 normalized pair visits. The generated endpoint
graph is intentionally a selected shallow family, not an enumeration of every
one-node regular graph.

A seeded search generates 320 bounds from 2–4 graph slots, then compacts the
union of the two endpoint reachability cones. The resulting graph sizes are
1:40, 2:160, 3:92, and 4:28; 133 bounds contain a directed cycle. Each bound
is checked under 48 pairs of closed regular assignments, for 15,360 more
differential checks. The recursion set includes one-node self-cycles and
multi-node cycles. A separate cyclic witness has two distinct recursive
Function roots and one retained argument residual: `x=A` succeeds and `x=B`
fails under both direct and normalized comparison.

## Model defects found and repaired

The first executable draft copied assignment graphs without offsetting their
local child references. Direct and normalized checks shared that bad copied
graph, so their agreement did not expose the defect. Independent review
produced the small witness `x = {a: self}` compared with `{a: A}`; the initial
copy incorrectly made the recursive child point into the bound graph. The
copy now offsets every imported Function/Record edge, and a separate assertion
checks both the copied self-edge and the expected rejection of that comparison.

The first random-bound generator also set the two query endpoints equal,
reducing its recursive checks to reflexivity. It now selects endpoint roots
independently (so equality is possible) over the compact union of both
reachable regions, requires an unresolved variable in that union, and reports
the actual post-compaction size histogram.
These were checker defects, not counterexamples to residual normalization.

## Boundary and next use

This model tests pure structural normalization on finite regular assignments.
It does not model lexical scope guards, stable `nu,K,D` contexts, arbitrary
joint `Phi`, effectful Function ports, open Record syntax, source generation,
or production solver acceptance. The finite run characterizes the recursive
part of the single-bound normalization claim only; it does not prove the
principal constrained residual presentation or effective joint projection.

Focused command: `python3 -B tools/research_regular_residual_factorization.py`.
It passes with the counts above; `git diff --check` passes. No Cargo tests were
run because this isolated checker changes no compiler code. The next structural
playground step is to carry the same recursive graph assignments jointly across
multiple residual bounds and a retained correlated finite `Phi`, extending the
existing acyclic joint-projection checker without changing the carrier.
