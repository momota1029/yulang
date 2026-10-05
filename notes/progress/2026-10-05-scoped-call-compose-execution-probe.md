# Scoped call/compose execution correspondence probe

Date: 2026-10-05
Status: finite characterization only; no source typing, solver, or production authority
Scope: differential execution of canonical `call` and `compose` Value-entry trees
Governing sources: [typed computation core](../design/2026-10-02-typed-computation-core-elaboration.md) §§3,6 and [ordinary computation semantics](../design/2026-10-02-ordinary-computation-semantics-package.md) §§3–4
Review: independent compiler-referee review found no blocking, major, or minor finding within this bounded model

[`tools/research_scoped_compose_execution.py`](../../tools/research_scoped_compose_execution.py)
compares two separately implemented evaluators for the canonical scoped bodies
`call f x = f x` and `compose f g x = f (g x)`. It compares a recursive
source-expression interpreter with a generated-core stack machine. Both use
the same finite expression/primitive inputs and observation vocabulary, but
they do not share an evaluator or continuation implementation. Source `Apply`
nodes have distinct occurrence IDs; the lexical environment is recorded as the
active binder scope.

The checked transition shape is delayed argument construction, receipt, Value
entry through `Force`, result rebind, body execution, and return. For a
suspending `g`, the model returns a pending request together with its source
origin, current state, trace, and remaining continuation suffix. Resumption
uses the supplied response and state without replaying receipt and preserves
the outer `f` suffix. `f` can observe the resumed state.

The finite domain has two values, two states, two `g` modes (return/request),
and two `f` modes (observe state / xor state). It covers 32 expression/input
cases, 64 response-path comparisons, 40 pending-prefix observations, and 56
completed observations. Four deliberate core-machine mutants are rejected:
eager argument force before receipt, replayed receipt on resumption, collapsed
application occurrences, and dropped pending continuation suffix. Shrinking
is exhaustive only within the declared finite domain; all four reported
witnesses are smallest in that enumeration.

Verification:

```text
python3 tools/research_scoped_compose_execution.py
  32 cases; 64 response-path comparisons; 40 pending-prefix observations;
  56 completed observations; all four mutants killed
python3 -B tools/research_scoped_compose_execution.py
  same result under independent compiler-referee review
```

This probe does not parse or lower Yulang source, construct production HIR,
infer types, interpret `(nu,K,D)`, or define Function membership, capture,
subtraction, callback admission, principal schemes, or Theorem C adequacy. Its
primitives are supplied finite `Int -> Int` relations, with at most one
request in an execution. It is operational characterization for the
`Force(D) >>= rebind >>= body` seam, not the source-to-endpoint theorem. The
next callback gate remains the comparison-independent complete Function
membership/admission interpretation and its actual-to-checked containment;
production inference replacement remains gated by soundness and principality.
