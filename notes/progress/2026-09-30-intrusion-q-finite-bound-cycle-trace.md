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
identity and empty weights.

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

## Bound-record provenance observed

A second instrumentation point read `TypeBounds::record` and the associated
constraint replay trace immediately after the first root compaction at
`TypeVar(0)` / epoch 27. It resolves the named q-cycle records as follows:

```text
BoundRecordId(1), TypeVar(4) lower PosId(4)
  <- ConstraintRecordId(1), root origin UnknownInternal
BoundRecordId(3), TypeVar(4) upper NegId(6)
  <- ConstraintRecordId(2), root origin UnknownInternal
BoundRecordId(4), TypeVar(1) lower PosId(4)
  <- ConstraintRecordId(3), replay UpperBoundAdded at TypeVar(4), premises 1 and 3
BoundRecordId(7), TypeVar(2) upper NegId(12)
  <- ConstraintRecordId(6), root origin ApplicationArgument
```

All four are ordinary bounds with empty weights. Constraints 1 and 2 have no
structural, row, or replay parents; constraint 3 has the recorded replay
derivation and complete replay provenance; constraint 6 has no structural,
row, or replay parents and complete replay provenance. This closes the local
recorded provenance graph for these incidence edges at the first snapshot:
record 4 is derived from records 1/3, while record 7 is independently rooted
in an application-argument constraint. Thus the typed graph is cyclic but
this local provenance graph is a finite acyclic derivation fragment.

The source trace ties constraint 6 to the exact `x f` occurrence in
`pub f x = x f`: it logs `SourceBoundaryId(0)` / `OriginId(2)`, callee value
`TypeVar(2)`, argument value `TypeVar(1)`, and byte ranges application `10..14`,
callee `10..11`, argument syntax node `12..14` (starting at `f` and including
the trailing newline). Frozen `tail.rs::make_source_app` allocates
that origin as `ApplicationArgument`; `make_app_with_origins` constructs
`Pos::Var(callee.value) <: Neg::Fun` with `Pos::Var(arg.value)` in the Function
argument. This matches constraint 6's endpoint
`Pos::Var(TypeVar(2)) <: Neg::Fun(arg=Pos::Var(TypeVar(1)))` and bound 7.
The TypeVar2/TypeVar1 child-node shapes are logged in the collector trace
above. This gives a fixture-local source occurrence/value map for the
application edge. Resolved HIR/DefId identities are inferred from the exact
ranges and lowering path, not separately printed.

The provenance/source command, on the same disposable Oracle worktree, was:

```text
YULANG_QORIGIN_TRACE=1 CARGO_TARGET_DIR=/tmp/yulang-intrusion-qorigin-target \
  cargo test -p infer --lib scratch_qorigin_self_application -- --nocapture
```

Result: 1 passed. Independent compiler-referee review checked the record,
constraint, and source-boundary links against source. This does not identify
source spans or binder identities behind the `UnknownInternal` roots, prove a
causal derivation from constraint 3 to constraint 6, or cover other records
and iterations.

## Limits and next proof obligation

- The finite **typed bound graph** cycle and the local derivation fragment are
  observed. The derivation fragment is acyclic; it is not a proof-provenance
  cycle and it does not connect constraint 3 causally to constraint 6.
- The source span/value map is established only for application constraint 6
  and upper bound 7. Internal constraints 1/2 remain rooted only at
  `UnknownInternal`; their source spans/binders are not recorded.
- Effect-variable paths are only partially traced. This is not a complete
  root/epoch graph, and the trace does not include final scheme quantifiers,
  interval restoration, or use-site behavior.
- Compact occurrences still do not carry the bound-record and parent-path IDs
  that distinguish the graph edges above.

Next, connect the selected typed graph and each evidence premise to a
finite-regular-presentation map, resolve source/binder identities for the
internal origins and complete the effect paths, then prove the Oracle's
q-erasure preserves the required root/use observations. Keep typed-bound
incidence and proof provenance as separate objects in that argument.
