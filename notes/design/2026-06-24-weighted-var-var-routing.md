# Weighted var-var routing plan

This note records the next solver optimization direction after replay duplicate
prefiltering.

## Current observation

`examples/showcase.yu` still spends most constraint time in bound replay even
after duplicate/trivial replay actions are prefiltered.

Observed with `check-poly-std`:

```text
constraint.replay_generated: 659985
constraint.replay_accepted: 62818
constraint.replay_duplicate: 585117
constraint.replay_prefiltered: 597104
constraint.replay_prefilter_duplicate_var_var_key: 553498
constraint.lower_replay_var_var: 352835
constraint.upper_replay_var_var: 266371
```

The dominant duplicate class is var-var replay. Terminal weight erasure and
row-tail duplicate categories are small:

```text
constraint.replay_prefilter_duplicate_terminal_erased: 6
constraint.replay_prefilter_duplicate_row_tail: 3844
```

## Rejected local optimizations

### Replay action capacity

Replacing `SmallVec::with_capacity(replay_input_count)` with `SmallVec::new()`
was slower in release bench. Even after prefiltering, enough accepted replay
actions remain that repeated growth costs more than the saved allocation.

### Exact compose cache

An exact `(ConstraintWeights, ConstraintWeights) -> ConstraintWeights` cache was
also slower despite an excellent hit rate. A temporary profile found only 318
unique compose inputs for 659,985 replay compose calls, but using the raw
`ConstraintWeights` pair as a `HashMap` key made clone/hash cost dominate.

Release / repeat 5 / `iter >= 2`:

```text
base:  infer 541.8ms, constraint.drain 226.1ms, total 603.6ms
cache: infer 567.8ms, constraint.drain 251.8ms, total 630.0ms
```

If weight caching is revisited, it should use interned weight IDs rather than
raw weight structures as keys.

## Shadow frontier result

`YULANG_REPLAY_FRONTIER_SHADOW=1` records a conservative var-var bound frontier:

```text
(side, pivot var, endpoint var, normalize_for_var_var_replay_key(weights))
```

On `examples/showcase.yu`:

```text
constraint.replay_frontier_shadow_var_var_candidates: 128178
constraint.replay_frontier_shadow_var_var_hits: 0
```

This means the replay duplicates are not caused by inserting the same var-var
bound fact into the same pivot table. Each bound insertion is locally novel.
The duplicate appears after joining that locally novel bound with the opposite
table.

## Shadow routing result

`YULANG_REPLAY_ROUTING_SHADOW=1` records accepted var-var canonical constraints
in an unweighted directed graph and checks whether the new endpoint edge was
already reachable before insertion.

On `examples/showcase.yu`:

```text
constraint.replay_routing_shadow_var_var_accepted_edges: 64971
constraint.replay_routing_shadow_var_var_repeated_endpoint_edges: 1796
constraint.replay_routing_shadow_var_var_reachable_before_edges: 54059
constraint.replay_routing_shadow_var_var_graph_nodes: 11403
constraint.replay_routing_shadow_var_var_graph_edges: 63175
```

This is only an unweighted shadow, so it is not a sound skip condition. It does
show that the major remaining redundancy is transitive var-var consequence
materialization rather than local bound-table duplication.

## Required invariant

For every variable `v`, lower bound `L(v, p, wl)` and upper bound `U(v, n, wu)`
still imply:

```text
C(p, n, wl * wu)
```

A routing optimization must preserve all distinct canonical consequences that
can affect later propagation, handler hygiene, row subtraction, and public
normalization.

Therefore, the solver must not collapse weighted var-var paths merely because
the endpoints are graph-reachable. Stack weights are not ordinary graph labels:

- non-empty weights can carry private evidence,
- var-var replay uses endpoint-sensitive normalization,
- same-boundary alias-cycle subsumption is a termination guard, not type
  equality,
- handler-visible subtraction depends on directed weight composition.

## Candidate design

Treat var-var constraints as a directed weighted routing graph, separate from
ordinary constructor bounds.

For a canonical var-var constraint:

```text
Pos::Var(a) <: Neg::Var(b) @ w
```

store a directed edge:

```text
a --w--> b
```

Then propagate non-var bounds through the graph instead of eagerly
materializing every transitive var-var consequence:

- a lower fact at `a` flows forward along outgoing edges,
- an upper fact at `b` flows backward along incoming edges,
- a `(component/path-summary, fact-key)` pair is processed once,
- raw evidence remains available separately from the active propagation
  frontier.

This is conceptually different from the existing `var_adjacency`, which is an
unweighted neighbor graph used by later reachability/compaction logic.

## Shadow-first implementation order

1. Add exact `WeightId` interning for `ConstraintWeights` or a narrower
   replay-weight normal form.
2. Add a shadow weighted routing graph that records var-var edges but does not
   change replay behavior.
3. Compute path summaries with exact composition and the same
   `normalize_for_var_var_replay_key` used by canonical var-var replay.
4. For each currently generated var-var replay consequence, ask the shadow
   graph whether the same canonical consequence was already known.
5. Record:
   - generated var-var consequences,
   - shadow-known consequences,
   - shadow-missed consequences,
   - shadow false-skip candidates.
6. Only after false-skip candidates stay at zero on the hardening fixtures,
   switch var-var replay emission to the routing frontier.

## Non-goals

- Do not use the unweighted reachability shadow as a skip condition.
- Do not collapse weighted SCCs as type-variable equality.
- Do not route row-tail, terminal, or constructor bounds through this graph in
  the first slice.
- Do not remove `seen`; keep it as the final safety net.

## Tests to keep green

At minimum, run:

```text
cargo fmt --check
git diff --check
timeout 180s cargo test -q -p infer constraints -- --test-threads=1
timeout 300s cargo test -q -p yulang dump_poly_std -- --test-threads=1
timeout 420s cargo test -q -p yulang -- --test-threads=1
```

And measure:

```text
timeout 180s cargo run -q -p yulang -- --std-root lib check-poly-std examples/showcase.yu
YULANG_REPLAY_FRONTIER_SHADOW=1 timeout 180s cargo run -q -p yulang -- --std-root lib check-poly-std examples/showcase.yu
YULANG_REPLAY_ROUTING_SHADOW=1 timeout 240s cargo run -q -p yulang -- --std-root lib check-poly-std examples/showcase.yu
```
