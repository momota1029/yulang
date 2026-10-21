# R259 — local Types/Console evaluation roots

Status: primary-only conditional source derivation; no independent review.

On successful source lowering, the Types `id x = x` binding becomes a lambda
value. `answer = id 42` and `name = id "Yulang"` lower as applications and
classify as computations; with publication enabled they produce ComputedDef
roots. `pair = (answer, name)` classifies as a value when both name-reference
items are values, as the pinned name-reference owner constructs pure
Value-classified references and tuple evaluation follows item expansiveness.
The final `pair.say` and both Console statements enter the separate ordered
root-expression path.

This derives the sample-local root subsequence only:

```text
Types:   ComputedDef(answer), ComputedDef(name), Expr(pair.say)
Console: Expr(println ...), Expr(say: 1 + 2)
```

Imported initializer membership/order, name-to-DefId resolution, tuple demand
and caching, specialization, host-request reachability, the complete sample
behavior and all parent proofs remain open. Exact source pins and conditions
are recorded in `tasks/agent-loop/sprints/yulang2-local-evaluation-roots-20261021-r259.md`.
