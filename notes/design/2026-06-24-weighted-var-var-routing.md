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

`YULANG_REPLAY_WEIGHTED_ROUTING_SHADOW=1` records the same accepted var-var
constraints in a directed weighted graph. The shadow interns exact
`ConstraintWeights` values, composes path summaries with
`compose_for_replay(...).normalize_for_var_var_replay_key()`, and checks whether
the exact endpoint / canonical-weight path already existed before adding the
new edge.

With the default per-edge search limit of 4096 states:

```text
constraint.replay_weighted_routing_shadow_var_var_accepted_edges: 64971
constraint.replay_weighted_routing_shadow_var_var_reachable_before_edges: 53409
constraint.replay_weighted_routing_shadow_var_var_capped_searches: 580
constraint.replay_weighted_routing_shadow_var_var_search_states: 3150858
constraint.replay_weighted_routing_shadow_var_var_weight_count: 43803
constraint.replay_weighted_routing_shadow_var_var_compose_cache_hits: 3043531
constraint.replay_weighted_routing_shadow_var_var_compose_cache_misses: 106747
```

Raising `YULANG_REPLAY_WEIGHTED_ROUTING_SHADOW_LIMIT` to 65536 did not change
the reachable count, but it increased search states to 38,786,058 and interned
weights to 745,711. The default limit should stay conservative.

The same shadow also queries each canonical var-var replay consequence during
generation, before consulting `seen`:

```text
constraint.replay_weighted_routing_shadow_var_var_consequence_queries: 607156
constraint.replay_weighted_routing_shadow_var_var_consequence_known: 606433
constraint.replay_weighted_routing_shadow_var_var_consequence_known_unseen: 52935
constraint.replay_weighted_routing_shadow_var_var_consequence_unknown: 723
constraint.replay_weighted_routing_shadow_var_var_consequence_unknown_seen: 0
constraint.replay_weighted_routing_shadow_var_var_consequence_capped_searches: 670
```

`known_unseen` is the key number: the current solver would enqueue a new
canonical var-var consequence, but the weighted routing graph already has an
exact path for the same endpoint and canonical weight. On `showcase`, this
accounts for 52,935 consequences.

The first weighted shadow inserted every accepted edge into the graph. That can
overstate a future optimization, because a real routing frontier would omit
edges that are already represented by an exact path. The next shadow keeps a
second frontier graph and does not insert an accepted edge when the frontier
graph already reaches the same endpoint with the same canonical replay weight.
The real solver still enqueues everything; this is only a skip simulation.

On `examples/showcase.yu`, the frontier simulation gives:

```text
constraint.replay_weighted_routing_shadow_var_var_accepted_edges: 64971
constraint.replay_weighted_routing_shadow_var_var_frontier_inserted_edges: 11480
constraint.replay_weighted_routing_shadow_var_var_frontier_skipped_edges: 53491
constraint.replay_weighted_routing_shadow_var_var_frontier_capped_searches: 498
constraint.replay_weighted_routing_shadow_var_var_frontier_search_states: 2519049
constraint.replay_weighted_routing_shadow_var_var_frontier_graph_edges: 11480
```

The consequence queries stay almost as strong on the frontier graph:

```text
constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_known: 600772
constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_known_unseen: 52899
constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_unknown: 6384
constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_unknown_seen: 5625
constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_capped_searches: 6331
```

This means the transitive routing signal survives after omitting redundant
edges: `known_unseen` drops only from 52,935 to 52,899. However, the naive
search is not itself an optimization. With both all-edge and frontier queries
enabled, the shadow performs tens of millions of cached weight compositions.
A production skip needs an incremental path-summary frontier or another cheap
novelty index; it should not run this DFS for every replay candidate.

The route graph is monotone, so positive exact-path results can be cached
without invalidation. Negative results are not cached, because a later edge may
make them true. Adding this positive cache changes only the shadow query cost:

```text
constraint.replay_weighted_routing_shadow_var_var_frontier_inserted_edges: 11658
constraint.replay_weighted_routing_shadow_var_var_frontier_skipped_edges: 53313
constraint.replay_weighted_routing_shadow_var_var_consequence_frontier_known_unseen: 52809
constraint.replay_weighted_routing_shadow_var_var_route_cache_hits: 606433
constraint.replay_weighted_routing_shadow_var_var_frontier_route_cache_hits: 606307
constraint.replay_weighted_routing_shadow_var_var_route_cache_entries: 64971
constraint.replay_weighted_routing_shadow_var_var_frontier_route_cache_entries: 64971
constraint.replay_weighted_routing_shadow_var_var_compose_cache_hits: 12263305
constraint.replay_weighted_routing_shadow_var_var_compose_cache_misses: 212698
```

Compared with the uncached shadow, cached composition work drops from about
50.6M hits to about 12.3M hits. The exact frontier counts shift slightly because
the fixed search cap interacts with which paths have already been found and
cached. The conclusion is unchanged: the frontier graph still identifies about
52.8K consequences that the current `seen` table would not prefilter.

`YULANG_REPLAY_WEIGHTED_ROUTING_SUMMARY_SHADOW=1` tests a more eager
path-summary table. It maintains outgoing/incoming exact weighted paths and
closes a newly inserted path against existing prefixes and suffixes. The shadow
has its own cap (`YULANG_REPLAY_WEIGHTED_ROUTING_SUMMARY_LIMIT`, default
200,000 paths) because full all-pairs closure can be much larger than the
frontier graph.

With summary-only shadow on `examples/showcase.yu`:

```text
constraint.replay_weighted_routing_shadow_var_var_summary_observed_edges: 64971
constraint.replay_weighted_routing_shadow_var_var_summary_known_edges: 22433
constraint.replay_weighted_routing_shadow_var_var_summary_new_edges: 6773
constraint.replay_weighted_routing_shadow_var_var_summary_inserted_paths: 200000
constraint.replay_weighted_routing_shadow_var_var_summary_duplicate_paths: 20073452
constraint.replay_weighted_routing_shadow_var_var_summary_capped_insertions: 35767
constraint.replay_weighted_routing_shadow_var_var_summary_max_queue: 169586
constraint.replay_weighted_routing_shadow_var_var_summary_outgoing_nodes: 6309
constraint.replay_weighted_routing_shadow_var_var_summary_incoming_nodes: 4316
```

This is an important negative result. The summary table reaches the 200K path
cap after only 6,773 new direct accepted edges, while generating about 20M
duplicate path insertions. A full transitive path-summary frontier is therefore
too broad as a production replacement. A viable routing optimization probably
needs a narrower summary, such as per-pivot demand summaries, bounded positive
path caches, or a routing table coupled to lower/upper bound propagation rather
than all-pairs weighted closure.

An env-gated prototype also tried to skip replay var-var consequences directly
when the weighted frontier graph already had an exact path. This is not sound
against the current solver representation. The adversarial corpus passed, but
public-signature golden tests failed:

```text
unannotated compose:
  got      ('a ['b] -> 'c) -> ('d -> ['b] 'a) -> 'd -> 'c
  expected ('a ['b] -> ['c] 'd) -> ('e -> ['b] 'a) -> 'e -> ['c] 'd

apply:
  got      ('a -> 'b) -> 'a -> 'b
  expected ('a -> ['b] 'c) -> 'a -> ['b] 'c
```

Adding guards for row-tail variables and then for empty weights did not fix the
loss of public latent effects. The reason is structural: the routing graph can
prove a consequence for propagation, but generalization and public projection
currently read the materialized bounds/evidence. Dropping a direct var-var
constraint without teaching those later phases to read an equivalent routing
summary removes co-occurrence fuel and makes higher-order functions appear
pure.

Therefore, actual replay skipping should remain out of tree until one of these
is true:

- generalization consumes a routing summary as equivalent evidence,
- skipped var-var consequences are represented as lightweight read-only bounds,
- the skip condition is restricted to a class proven irrelevant to public
  projection and handler hygiene.

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

1. Keep the current weighted routing shadow as an opt-in measurement tool.
2. Add a real routing frontier for var-var replay consequences, still shadowed:
   - consult the weighted graph before materializing a var-var replay action,
   - record whether the skipped candidate would have been accepted by `seen`,
   - keep emitting the action until the shadow has no false skips.
3. Once stable, switch only var-var replay emission to the routing frontier.
   Keep non-var bounds, row tails, terminal endpoints, and constructor bounds on
   the current replay path.
4. Keep `seen` as the final safety net after the routing frontier is enabled.

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
