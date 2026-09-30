# Q finite bound-cycle trace

Date: 2026-09-30
Scope: one frozen Yulang2 Oracle fixture, `pub f x = x f`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: fixture-level source evidence; not a design approval or general theorem

## Method

A disposable worktree added trace-only logging around scheme-projected lower
and upper bound collection and typed-node traversal. The focused Rust test ran
`dump_source("pub f x = x f\n")` and checked that lowering reported no errors:

```text
YULANG_QPREMISE_TRACE=1 CARGO_TARGET_DIR=/tmp/yulang-intrusion-qpremise-target \
  cargo test -p infer --lib scratch_qpremise_self_application -- --nocapture
```

Result: 1 passed. An independent compiler-referee pass matched the trace to the
frozen collector and projection-evidence definitions. The instrumentation and
scratch test were discarded with the disposable worktree; no Oracle source was
changed.

## Typed bound graph observed

The collector trace directly records this finite, empty-weight cycle:

```text
TypeVar(2)- --upper BoundRecordId(7)--> NegId(12): Fun.arg PosId(8)
PosId(8) = Var(TypeVar(1)+)
TypeVar(1)+ --selected lower BoundRecordId(4)--> PosId(4): Fun.arg NegId(4)
NegId(4) = Var(TypeVar(2)-)
```

Each named type edge and its endpoint is visible in the trace. The root
`TypeVar(0)+` selected lower record 24 enters through `PosId(19)`, a Function
whose argument is the same `NegId(4)` node. This establishes the typed-bound
incidence cycle for this captured collector run, including its shared node
identity and empty weights. It does not establish a cycle in the proof
provenance graph.

## Projection evidence attached to the selected records

`TypeVar(1)` lower record 4 is included with `DecisiveClaimedArm` evidence: a
`ReplayConjunction` at pivot `TypeVar(4)`, using lower record 1 and upper record
3, attributed to replay constraint 3. The pivot records have these endpoints:

```text
TypeVar(4) lower record 1: PosId(4) = Fun(arg = NegId(4) = Var(TypeVar(2)))
TypeVar(4) upper record 3: NegId(6) = Var(TypeVar(1))
```

Record 1 itself is later returned as `Unclaimed` when queried as a lower for
`TypeVar(4)`. Record 4's evidence therefore records one replay derivation; it
does not provide the complete provenance graph.

At the root, `TypeVar(0)` lower record 24 is likewise a `ReplayConjunction` at
pivot `TypeVar(14)`, using lower record 21 and upper record 23, attributed to
constraint 17. Record 21 ends at the same root Function `PosId(19)`, and record
23 ends at `Var(TypeVar(0))`. Both records 22 and 24 carry uncovered claim 14
in their projection reason; record 22 is a standalone original from
constraint 16. These are exact trace observations, not claims that every
underlying proof premise is independently accepted.

## Limits and next proof obligation

- The finite **typed bound graph** cycle is observed; no finite
  **proof-provenance cycle** is established. In particular, selected upper
  record 7 has no proof parent/origin in this trace.
- Trace IDs do not establish a source-span/constraint-origin map from `pub f x
  = x f` to each named bound record.
- Effect-variable paths are only partially traced. This is not a complete
  root/epoch graph, and the trace does not include final scheme quantifiers,
  interval restoration, or use-site behavior.
- Compact occurrences still do not carry the bound-record and parent-path IDs
  that distinguish the graph edges above.

Next, connect the selected typed graph and each evidence premise to a
finite-regular-presentation map, then prove the Oracle's q-erasure preserves
the required root/use observations. Keep typed-bound incidence and proof
provenance as separate objects in that argument.
