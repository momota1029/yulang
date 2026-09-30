# SCC intrusion for Simple-sub-style generalization — design sketch

- Date: 2026-09-29
- Status: **Exploratory / non-authoritative / unproved**
- Scope: type-inference redesign notes only
- Implementation authority: **none**
- User origin: idea proposed directly by the author during discussion of the current Yulang3 F5/F5c debt
- Important: this note is design material for a possible solver reboot. It does **not** amend the current F5 contract, authorize changes to `yulang3`, or claim soundness/principality.

## 1. Motivation

The current Yulang3 F5/F5c path has accumulated substantial machinery around
generalization, recursive binders, resource accounting, owner/event replay, and
closed-scheme construction. The guarded-cycle investigation additionally shows
that the current F5 scheme-shape contract can require exponentially many
distinct reachable Function subgraphs for the guarded-cycle family.

Separately, the old Yulang implementation deliberately generalizes SCC members
one by one. This is a conservative choice: although Simple-sub extrusion
already handles cyclic *type-variable bound graphs*, we do not currently have
a proof that a mutually recursive *definition SCC* can be generalized in one
step while preserving the intended principal result.

The proposal below is intended to make that missing theorem small enough to
study directly.

## 2. Core idea: intrusion

Working name: **intrusion**.

Suppose a solved/frozen SCC contains inference variables at an inner level, and
we need to expose the SCC across an outer generalization boundary.

For each boundary-relevant variable `v`, allocate an outer-level **parent
variable** `p(v)` and register the relationship on `v`.

Conceptually:

```text
inner SCC                    outer boundary

a -------------------------> a'
b -------------------------> b'
c -------------------------> c'

a.parent = a'
b.parent = b'
c.parent = c'
```

After parent allocation, boundary-facing uses of an inner variable are replaced
by its registered parent. The SCC topology itself remains a graph; it is not
expanded into a tree merely to construct a closed scheme.

This can be viewed as a batched version of Simple-sub extrusion: ordinary
extrusion discovers a cyclic reachable bound graph recursively and memoizes
fresh low-level representatives. If the SCC is already known, intrusion
pre-allocates the relevant representatives and then rewrites/relates the graph
against that fixed map. This is only a structural analogy so far. Simple-sub
indexes representatives by `(variable, polarity)` and mutates source-side
bounds as it discovers them. A valid batching simulation must preserve those
polarity-specific representatives, link writes, bound snapshots, and first-
visit order; an endpoint rename through one SCC vertex map is not enough.
Details are recorded in
[`2026-09-30-simple-sub-extrusion-preallocation-lemma.md`](../progress/2026-09-30-simple-sub-extrusion-preallocation-lemma.md).

## 3. Cost hypothesis

Let the frozen SCC graph have `V` relevant variables and `E` relevant bound
edges.

Parent allocation is `O(V)`; applying the parent map to the SCC edges is
`O(E)`. Thus the expected asymptotic cost is

```text
O(V + E)
```

which is the same order as traversing the same reachable cyclic bound graph
during ordinary extrusion.

This is only a complexity hypothesis until the exact representation and
polarity rules are fixed.

## 4. Relation to ordinary Simple-sub extrusion

This proposal should preferably be justified as an implementation strategy for
ordinary extrusion, not as a new semantic rule.

A possible proof route is:

1. **Preallocation lemma.** Preallocating fresh names keyed by `(VarId,
   polarity, boundary)` and replaying the exact first-visit transition sequence
   is alpha-equivalent to on-demand allocation. This conditional statement is
   now characterized for Simple-sub's operation. It does not establish that
   SCC root order can change, that polarities can share a parent, or that the
   proposed Yulang boundary rewrite is equivalent.
2. **Edge preservation lemma.** Rewriting/relating each relevant bound edge
   through the parent map produces exactly the constraints that recursive
   extrusion would produce.
3. **Cycle closure lemma.** A back edge in the SCC returns to the already
   allocated parent representative, so no duplicate representative is created.
4. **Root-order independence.** Still open. A fixed name map alone does not
   establish order independence: extrusion mutates source bounds, and later
   polarity visits can observe earlier link writes. In a two-call variable-only
   probe, opposite root orders produce different raw bound graphs but the same
   assignment fiber; see
   [`2026-09-30-simple-sub-extrusion-root-order.md`](../progress/2026-09-30-simple-sub-extrusion-root-order.md).
   The proof criterion must therefore be the scheme/assignment relation, not
   graph alpha-equivalence. Prove adjacent root-transition swaps preserve that
   relation under explicit side conditions, or retain the Oracle's order. A
   reviewed conditional swap argument covers independent Simple-sub extrusion
   calls on a frozen graph; it does not model Yulang root preparations that
   advance shared constraints. See the linked progress record.
5. **Generalization simulation.** Generalizing the intruded component and then
   instantiating it with fresh parent substitutions has the same constraint
   consequences as re-establishing the original monomorphic SCC at a fresh use
   site.

The current note does not prove any of these statements.

## 5. Polarity is an open proof obligation

A naive identity alias

```text
v == parent(v)
```

may collapse to merely lowering the level of `v`, which is not automatically
equivalent to Simple-sub extrusion.

The reference design must therefore decide whether the parent map is

```text
(VarId, Polarity, BoundaryLevel) -> ParentVar
```

as in ordinary polarity-sensitive extrusion, or whether SCC structure permits a
stronger parent-sharing theorem.

Do **not** identify positive and negative representatives merely for
convenience without a proof.

## 6. Freeze boundary

The simplest version assumes:

```text
collect constraints
-> solve SCC to a fixed point
-> freeze the SCC
-> intrude at the target boundary
-> generalize
```

After freezing, inner bound rows relevant to the component are immutable.
This avoids a parent/child synchronization protocol.

A design that allows new bounds to arrive after intrusion needs a separate
incremental correctness argument and is out of scope for this sketch.

## 7. Generalized component as the internal authority

Instead of immediately forcing each mutually recursive definition into an
independent closed tree/DAG scheme, consider an internal authority of the form:

```text
GeneralizedComponent {
    roots: DefId -> Root,
    parents: InnerVar -> BoundaryVar,
    graph: frozen generalized SCC graph,
}
```

An individual definition scheme is a projection of this component rather than
the primary authority.

This preserves SCC sharing and recursion across the generalization boundary and
may avoid the path-expansion pressure seen in the current F5c closed-scheme
construction.

This is a representation proposal, not yet a compatibility claim for the
current public F5 scheme shape.

## 8. Monomorphization / specialization payoff

A major motivation for making the parent relation explicit is that the same map
can become the specialization interface.

At a use site, instantiation chooses values for the parent variables:

```text
sigma(parent_a) = A
sigma(parent_b) = B
sigma(parent_c) = C
```

Because the child-to-parent relationship is retained explicitly, the same
substitution can be pulled back into the frozen SCC graph:

```text
a <- A
b <- B
c <- C
```

Thus generalization, instantiation, and monomorphization can share one boundary
representation instead of reconstructing correspondence from a closed scheme,
provenance graph, recursive-bound table, or post-hoc variable matching.

A plausible specialization cache key is therefore based on

```text
(ComponentId, substitution restricted to boundary parents)
```

rather than the entire internal constraint graph.

This is expected to simplify specialization substantially, but the exact
treatment of inner variables with no parent remains to be specified.

## 9. Not every inner variable necessarily needs a parent

The minimal interface should distinguish variables whose freedom crosses the
generalization boundary from variables that remain entirely internal.

A possible shape is:

```text
parent: Option<BoundaryVar>
```

Only boundary-relevant variables receive parents. Purely internal variables can
remain component-local and be solved, eliminated, or retained according to the
component representation.

The criterion for parent creation is part of the missing proof.

## 10. Why this may matter for the current F5c failure mode

The current guarded-cycle investigation shows two different exponential
effects:

- path-sensitive production enumerates exponentially many occurrences;
- under the current closed F5 scheme-shape contract, successful guarded-cycle
  output can itself contain exponentially many distinct reachable Function
  subgraphs.

Intrusion does **not** by itself prove that those outputs can be compressed
without semantic change. However, it changes the design question: if the
authoritative generalized object may remain an SCC graph with explicit
boundary parents, then we need not assume in advance that every recursive
component must first be expanded into the current closed per-root scheme shape.

Whether this permits a compact Oracle-equivalent representation is a separate
proof obligation.

## 11. Suggested first proof fixtures

Before implementation, work the proposal by hand on at least:

1. identity: `my f x = x`;
2. simple mutual recursion: `f <-> g`;
3. a diamond-shaped bound graph with shared descendants;
4. nested let where an inner SCC crosses exactly one outer boundary;
5. a polarity-sensitive function example where positive/negative extrusion
   cannot be conflated;
6. guarded recursive Function bounds that currently trigger F5c path expansion.

For each example compare:

- ordinary Simple-sub extrusion;
- proposed SCC intrusion;
- generalized component;
- fresh instantiation;
- monomorphization by parent substitution.

## 12. Non-goals

This note does not:

- prove soundness or principality;
- authorize replacing current F5c;
- authorize a new public scheme representation;
- claim that all guarded-cycle outputs admit compact representation;
- define method/role/effect-row behavior;
- define incremental post-intrusion mutation;
- define the final serialization/cache ABI.

Those require separate review and, where they change an Authoritative contract,
explicit user approval.
