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

For each boundary-relevant variable-and-polarity port `(v, p)` at the target
boundary `B`, allocate an outer-level representative `parent(v, p, B)` and
register that relationship. One SCC vertex may therefore have more than one
boundary representative. The diagram below shows the polarity-port shape;
neither it nor the key specifies which variables are boundary-relevant.

Conceptually:

```text
inner SCC                    outer boundary

a⁺ ------------------------> a⁺'
a⁻ ------------------------> a⁻'
b⁺ ------------------------> b⁺'
b⁻ ------------------------> b⁻'

parent(a,+,B) = a⁺'
parent(a,-,B) = a⁻'
...
```

After parent allocation, each boundary-facing occurrence is related to the
parent port selected by its extrusion call and polarity. The SCC topology
itself remains a graph; it is not expanded into a tree merely to construct a
closed scheme.

This can be viewed as a batched version of Simple-sub extrusion: ordinary
extrusion discovers a cyclic reachable bound graph recursively and memoizes
fresh low-level representatives. If the SCC is already known, intrusion
pre-allocates the relevant representatives and then rewrites/relates the graph
against that fixed map. This is only a structural analogy so far. Simple-sub
indexes representatives by `(variable, polarity)` within an extrusion call and
mutates source-side bounds as it discovers them. The separate-polarity
discriminator in the audit has `L(v)=[Int]` and `U(v)=[]`: the positive and
negative representatives admit distinct boundary choices `Top` and `Bottom`,
while identifying them loses that pair of choices. So a shared parent across
polarities is already refuted for ordinary Simple-sub equivalence by this
case; it would require a different semantic theorem and an explicit account
of the lost solution. A valid batching simulation must preserve polarity-
specific representatives, link writes, bound snapshots, and first-visit
order; an endpoint rename through one SCC vertex map is not enough.
Details are recorded in
[`2026-09-30-simple-sub-extrusion-preallocation-lemma.md`](../progress/2026-09-30-simple-sub-extrusion-preallocation-lemma.md).

## 3. Cost hypothesis

Let the frozen SCC graph have `V` relevant variables and `E` relevant bound
edges, and let `P` be the number of required variable/polarity/boundary ports
in the chosen extrusion call.

The earlier `O(V + E)` estimate assumed one parent per variable and is not
justified by the polarity-sensitive reference. A port-based pass would cost
`O(P + E_P)`, where `E_P` counts bound-edge incidences visited through those
ports. Relating that quantity to `V + E` depends on the graph and port
allocation rule; it remains a complexity hypothesis.

```text
O(P + E_P)
```

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

The reference-compatible candidate parent map is

```text
(ExtrusionCall, VarId, Polarity, BoundaryLevel) -> ParentVar
```

This key shape matches ordinary polarity-sensitive extrusion. Whether a more
compact successor relation can quotient any of these ports is an independent
soundness and principality question; it is not a way to claim ordinary
extrusion equivalence by default. Boundary ownership and the criterion for
allocating a port remain open.

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
    parents: (ExtrusionCall, InnerVar, Polarity, BoundaryLevel) -> BoundaryVar,
    graph: frozen generalized SCC graph,
}
```

This is a candidate port map, not an endorsed representation. The displayed
key includes the call identity because the reference cache is local to one
extrusion call; a component-wide identity needs its own scope argument.

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

For a fixed generation call `k`, the component contains its boundary ports.
Each independent incoming use `u` applies its own freshening substitution to
those ports; it does not reuse another use's instantiated identities:

```text
sigma_u(parent(k,a,+,B)) = A_u
sigma_u(parent(k,a,-,B)) = B_u
sigma_u(parent(k,c,+,B)) = C_u
```

Because the child-to-parent relationship is retained explicitly, the same
substitution can be pulled back into the frozen SCC graph:

```text
a⁺ <- A_u
a⁻ <- B_u
c⁺ <- C_u
```

Thus generalization, instantiation, and monomorphization can share one boundary
representation instead of reconstructing correspondence from a closed scheme,
provenance graph, recursive-bound table, or post-hoc variable matching.

A plausible specialization cache key is therefore based on

```text
(ComponentId, substitution restricted to boundary ports for use `u`)
```

rather than the entire internal constraint graph.

This is expected to simplify specialization substantially, but the exact
treatment of inner variables with no parent remains to be specified.

## 9. Not every inner variable necessarily needs a parent

The minimal interface should distinguish variables whose freedom crosses the
generalization boundary from variables that remain entirely internal.

A possible shape records a parent independently for each relevant port:

```text
parent: (ExtrusionCall, InnerVar, Polarity, BoundaryLevel) -> Option<BoundaryVar>
```

Whether ports persist at component scope or are recreated per boundary
operation remains open. Every incoming use still gets an independent
capture-avoiding freshening map.

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
