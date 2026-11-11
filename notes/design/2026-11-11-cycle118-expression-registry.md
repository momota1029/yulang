# Annotated scalar expressions to real registry dictionaries

Status: Draft. Scope: I-16 P1/P2. Reduce `frontierLocal` and `evidenceNode` by
removing the caller-provided ordinary state and receiver slot from cycle118's
scalar registry adapter. This is a new outer entry for the same finite fragment,
not a new expression language or a general source B4 instance.

Inputs are an existing `Inference.Expr`, an explicit int/str annotation, a role,
and arbitrary finite real scalar declarations. The existing scalar-expression
checker supports closed literals, variables and let expressions. It computes
annotation validation; the adapter generates one actual ordinary slot and both
bounds, runs the real ordinary solver and materializer, then the existing
registry elaborator. The caller supplies no state, source slot, typed derivation,
selected declaration, model, or success proof.

The independent judgment is scalar `Evaluates` plus declaration-origin `Ready`.
It must be equivalent to the actual selected/no-implementation/ambiguous output.
For every returned dictionary and every value satisfying existing declarative
expression typing and the explicit annotation, the source-visible dictionary
must implement that value. The proof must refer to all such values, not the
single scalar representative used by the checker. Order and duplicate visibility
remain exact dictionary invariances.

Unsupported syntax or mismatched annotations yield unavailable in this adapter,
not a global language rejection. No effects, open source environments, parser AST,
where children, associated equations, or generalized annotations are introduced.
The existing expression typing/evaluation bridge is reused without editing it.
