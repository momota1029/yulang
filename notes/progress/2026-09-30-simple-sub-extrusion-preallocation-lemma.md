# Simple-sub extrusion: preallocation simulation boundary

Date: 2026-09-30
Status: reviewed candidate statement pending independent audit
Scope: operational characterization of `mlsub-compare` extrusion and the exact preallocation claim available to SCC intrusion
Source: Simple-sub paper §3.5.1, Fig. 7; `mlsub-compare` commit `9bae772624c23b52a93c1b226157e16898b4d9db`, `Typer.scala::extrude`

## Reference transition

Fix a target boundary level `B`. The reference operation has one cache per extrusion call, keyed by `(v,p)` with `p ∈ {+,−}`. Structural recursion preserves polarity through a constructor result and flips it through a Function argument. A variable at level `≤ B` is returned unchanged. For a variable `v` above `B`, the first visit allocates a fresh `w` at `B` and inserts `(v,p) ↦ w` into the cache **before** traversing bounds. A later visit to the same pair returns `w`, closing regular cycles. Opposite polarities use different cache entries and therefore different fresh variables.

Write `L(v)` / `U(v)` for the current ordered lower/upper bound lists at the instant a first visit begins. The first-visit side effects are:

```text
visit(v,+):
    allocate w; cache[(v,+)] = w
    prepend w to U(v)
    snapshot current L(v); set L(w) = map(extrude(_, +), snapshot)
    leave U(w) empty

visit(v,-):
    allocate w; cache[(v,-)] = w
    prepend w to L(v)
    snapshot current U(v); set U(w) = map(extrude(_, -), snapshot)
    leave L(w) empty
```

The lists are immutable values held in mutable variable fields. Each `map` reads a list value before descending through its elements. Recursive visits may prepend new bounds to a source variable; a later first visit can observe those writes, while an already-started map continues over its earlier list snapshot. Therefore the operational traversal order and the source-side link writes are part of the concrete simulation target. A proof based only on a fixed snapshot of original edges omits behavior.

## Conditional preallocation lemma

Model the implementation as small-step states containing the mutable bound
heap, the `(v,p) -> w` cache, the current expression, and a stack of pending
bound-list map continuations. A map frame records the source-list snapshot,
remaining elements, and already produced results. Its return step performs the
final assignment to `L(w)` or `U(w)` only after all nested calls return. This
stack is required because first-visit writes are nested; completion does not
follow simply by counting cache misses.

For one exact reference execution, let `K` be its ordered fresh-allocation
events. A second run may create empty, fresh nodes for all keys in `K` in
advance in a separate name table, but must start with an empty operational
cache. On a cache miss for `(v,p)`, it retrieves that key's reserved node,
installs the ordinary cache entry, performs the same source-side link write,
takes the same bound-list snapshot, and pushes the same map frame. Cache hits,
structural descents, list-element returns, and frame completion follow the
original order. Relate the heaps by the fixed injective name map on nodes that
have entered the cache; reserved but not-yet-entered nodes are unreachable
empty allocations. Relate caches, current expressions, and every continuation
frame pointwise by the same map. Each small step preserves this relation:
fresh allocation selects the mapped reserved node; all other transition kinds
make the same read, write, or stack change under the map. At termination all
allocated keys have been entered and the returned roots and mutated heaps are
alpha-equivalent. This proves name preallocation for a known trace, not a
faster algorithm for discovering that trace.

The lemma is intentionally narrow. It does **not** show that one may process
SCC vertices in a new order, replace both polarities with one parent, merely
rename edges without source-side link writes, freeze before all Oracle root
preparations, or use a parent substitution as a principal scheme interface.
Root-order independence needs another proof because first-visit ordering
affects which dynamically updated bound snapshots later visits can read.

## Two discriminator traces

### Productive cycle

Take a positive extrusion root `v` above `B`, with `L(v) = [Fun(Int,v)]`. The first visit allocates `q=(v,+)`, records `U(v) := [q] ++ U(v)`, then maps the lower snapshot. Traversing `Fun(Int,v)` flips polarity in the argument and preserves it in the result; `v` in result position finds `q` already cached. The resulting lower bound is `Fun(Int,q)`, so the representative graph contains the regular cycle `q` lower-bounded by `Fun(Int,q)`. No unfolding is needed. The preallocation replay must preserve both the early cache insertion and the `v.upper` link.

### Shared diamond

Take `L(v) = [Fun(a,c), Fun(b,c)]` and positive root `v`, with `v,a,b,c` above `B` and `a,b,c` initially unbounded. The map visits `a` and `b` at negative polarity, and `c` at positive polarity in each result. The first `c+` visit allocates `q_c`; the second returns that same representative. The result is shared at the diamond's join. This confirms that the memo key must retain the source identity and polarity; the two occurrences of `c+` share, while occurrences of one source variable at opposite polarities need not.

For the separate-polarity discriminator, use the expressible graph
`L(v)=[Int]`, `U(v)=[]`. The empty upper-bound intersection denotes semantic
Top; Top/Bottom are not constructors of the reference implementation's
`SimpleType`. Positive extrusion yields `Int ≤ p+`; negative extrusion copies
the empty upper list, so its upper condition is `p− ≤ Top`. Source-side
propagation also relates `p− ≤ p+` when both links are installed. The semantic
choices `p+=Top, p−=Bottom` satisfy those constraints. Identifying `p+` and
`p−` forces one value to satisfy both roles and cannot represent that pair of
boundary choices.

## Consequence for the intrusion candidate

The SCC sketch's “allocate representatives once, then rewrite/relate the graph” idea can claim Simple-sub extrusion equivalence only after it specifies the key set `(VarId, polarity, boundary)`, the source-side link writes, exact bound-list snapshots, first-visit order, and recursive cache behavior. A stronger root-order-independent or polarity-sharing parent relation is a distinct conjecture and must be compared against the correct `Root`/instance relation, not called the Simple-sub preallocation lemma.

The source baseline is now explicit enough to start a finite transition simulator or proof on paper. It remains short of Yulang Oracle adequacy: Oracle member-root projection, recursive-interval pruning, ordered root restarts, effects, and public scheme observations have separate obligations. In particular, the `pub f x = x f` negative-intersection projection correction remains unresolved.
