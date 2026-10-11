# Source-value reference SCCs and intrusion: semantic repair draft

Status: Draft
Scope: Clarify the graph used to qualify Value parent/copy intrusion and identify the missing source-to-solver bridge
Drafted-by: primary
Reviewed-by: spec_auditor (two delta reviews; no residual finding)
Supersedes: none; this draft has no authority

## Why this draft exists

The current parent-copy intrusion decision selects an operation: extrusion
retains a copy's actual parent, and intrusion equates parent and copy when they
enter the same Value SCC. It does not license deriving that SCC from subtype
comparisons or from whichever side of a bound stores a payload. Earlier
research used those operational payload references as if they were the
semantic Value-reference graph. That inference was invalid.

This draft repairs the graph statement and records the bridge still needed
before the existing operation can be characterized or its reachability proved.
It does not change Simple-sub typing, extrusion, generalization, or the selected
intrusion operation.

## Source-value reference graph: established example

Take the source:

```yulang
my host z = {
  my outer x = {
    my g y = outer g;
    x
  };
  outer
}
```

For this source abstraction, each binding owns its initializer/body value,
excluding initializer bodies of declarations nested inside that value. Put an
edge `f → g` exactly when a reference occurrence owned by `f` resolves to
binding `g`. A nested declaration's initializer contributes outgoing edges
from its own binding. This gives a source-binding abstraction of the example.
The selected semantic graph has Value variables as vertices and references in
their values as edges; whether and how the binding abstraction projects from
that graph is part of the still-open compiler bridge. Extrusion-created copies
are distinct Value vertices; their parent link does not identify or connect
them. The compiler bridge must show how each such vertex's actual
value-reference edges are constructed. The source-binding abstraction yields:

```text
host → outer
outer → x
g → outer
g → g
```

The owned value of `outer` ends at its result `x`; `g`'s initializer is owned
by `g`, so its references do not create `outer → g`. Lexical containment and
the fact that `g` is declared in `outer` do not create that edge. The
application in `g` contains references to `outer` and `g`, yielding the two
outgoing edges shown. The SCCs at this granularity are all singletons. `{g}`
is a cyclic singleton SCC because it has a self-loop; there is no nontrivial
SCC (no SCC containing two or more distinct vertices).

The HIR/source audit locators are `crates/yu-hir/src/module/local_source.rs`
(local binder installation and name resolution around lines 332–360, 636–657,
and 819–830). This example refutes the earlier candidate graph that added
`outer → g` from containment and any inference that a self-loop is not an SCC.

## Relations that must remain distinct

The following are different relations unless a source constructor supplies a
proved correspondence:

1. **Source reference:** an occurrence in a value resolves to a source binding.
2. **Solver constraint:** a generated subtype or Call obligation relates type
   variables/rows; the comparison itself is not a source-reference edge.
3. **Operational payload incidence:** a bound or residual recipe stores or
   replays a row/value payload. Its physical storage side alone does not make
   it a semantic reference edge.
4. **Extrusion ancestry:** a fresh solver Value variable records the parent
   from which it was copied. Parent metadata alone is not an edge in the
   source-reference graph.

The graph used by the approved intrusion operation must be specified using
actual Value-variable references in constructed values, including references
that cross extrusion-family levels. It cannot be reconstructed by reversing
all lower-bound edges, by using lexical scope, or by quotienting every copy to
its source binder.

## Missing bridge: source bindings to extrusion variables

The source-level example is at binding granularity; its correspondence to the
selected semantic graph remains to be proved. That graph has actual Simple-sub
Value variables as vertices, including
separate identities created by extrusion. Its edges must be actual references
in those variables' values. The bridge must identify the exact source
constructors that create each edge and show how constraint generation,
retained values, later calls, extrusion, and generalization construct or
transport those references. A binder SCC lifted after the fact cannot replace
this graph, because it would erase distinct parent/copy identities. Neither a
subtype comparison nor storage direction may be treated as the missing edge.

Until this bridge is established, the following claims remain OPEN:

- whether the retained parent/copy pair can occupy one SCC in a real
  supported inference history;
- whether current SCC processing computes the approved SCC relation;
- whether the parent/copy equality operation is required, reachable, or
  redundant on ordinary source programs;
- any soundness or principality result that depends on that qualification.

The affected payload-only analyses are specifically the `Q/P*` cycle in
`notes/theory/2026-10-11-ancestor-call-extrusion-scc.md` and the `R/V`
cycle in `notes/progress/2026-10-11-source-parent-copy-witness-search.md`.
Their inspected native solver transitions establish operational payload
incidence and extrusion events, but those artifacts do not derive their SCC
adjacency from the source-value ownership relation above. Their SCC membership
and exclusion conclusions therefore do not establish semantic SCC membership
or intrusion qualification. This is a gap in those artifacts' source bridge;
it does not imply that every lower/upper-stored incidence is irrelevant. Each
candidate edge must be traced to the actual value/reference constructor that
owns it. Other bounded derivations remain usable for their separately stated
operational claims.

## Scope of semantic repair

The correction is local to the meaning of Value references, SCC qualification,
and the bridge from source-value construction to solver parent/copy identity.
It does not require rewriting ordinary Simple-sub judgments, constraint
generation/propagation, levels, extrusion, generalization, or Effect semantics.
Those parts remain subject to their existing contracts. Any proof or
implementation conclusion depending on the old SCC graph must be re-evaluated
against the corrected relation; independent results need not be discarded.

## Decision required before authority can move

Formalize and justify the source-to-Value-variable edge construction. The
vertex domain and edge meaning above follow the user's direct clarification;
the unresolved work is the exact mapping, edge ownership for each source
constructor, treatment of shared captures and fresh uses, and how the selected
reference relation is faithfully computed as extrusion creates identities,
intrusion equates identities, and generalization publishes schemes. This asks
for correct graph construction/transport across those operations, not
unchanged SCC membership when an operation changes the vertices or equality
relation. Any stronger lifecycle invariant needs a separate statement and
justification. No compiler implementation change is authorized by this draft.

## Evidence and boundaries

- The source-binding edge list and singleton-SCC conclusion above are
  construction facts for the displayed source.
- HIR name-resolution locators identify where the source audit should be
  repeated if binder behavior changes.
- Independent conformance review found no residual issue in the source graph
  example, declaration ownership convention, relation boundaries, or the
  still-open source-to-Value-variable correspondence. The draft remains
  unapproved and non-authoritative.
- No test, build, or executable source-to-solver correspondence check is
  claimed here.
