# SCC intrusion abstract semantics — first draft

Date: 2026-09-29
Status: Draft; exploratory; not implementation authority
Scope: pure polarized type graphs and definition-SCC generalization
Approved-by: none
Approved-at: none
Drafted-by: primary agent
Reviewed-by: none
Supersedes: none

This draft advances Gate B of
[`2026-09-29-scc-intrusion-redesign-charter.md`](2026-09-29-scc-intrusion-redesign-charter.md).
It records a candidate mathematical interface, not a settled representation or
a soundness/principality result. F5 closed schemes are not the target.

## 1. Initial graph class

Start with finite regular graphs: cycles are represented by back-edges, never by
unfolding. The first proof fragment contains only `Bottom`, `Top`, atomic
constructors, variables, and polarized Functions. Function arguments reverse
polarity; results preserve it. Records and tuples may be added as covariant
products after the core lemmas. Effects, rows, methods, role constraints, and
handler hygiene are outside this fragment.

The graph has two kinds of identity:

- a **type vertex** identifies one shared unknown and owns its lower and upper
  bound edges;
- a **boundary port** identifies one independently substitutable exposure of
  that graph at a generalization boundary.

An edge records a polarized type endpoint and its direction. An endpoint is a
constant, a constructor applied to endpoints, a Function of endpoints, or a
reference to a type vertex. A lower edge records `endpoint <: vertex`; an upper
edge records `vertex <: endpoint`. This draft assumes bound closure reaches a
fixed point before the graph is frozen.

## 2. Enclosing environment and closure

At a boundary `B`, divide vertices into:

- **local** vertices allocated in the SCC being generalized;
- **outer** vertices owned by an enclosing environment;
- **rigid** vertices whose identity must remain shared and cannot be selected
  by this generalization.

The environment is part of the semantic input, not copied into the SCC. A local
vertex that reaches an outer/rigid vertex through either bound direction keeps
that exact outer identity. It must not receive a fresh local parent merely
because the path crosses the boundary. Reachability includes recursive and
shared back-edges and is graph traversal, not path enumeration.

An SCC is frozen only after all its member constraints have reached closure and
all dependency components needed by its roots are finalized. While open,
references among SCC members point to their live roots. No internal use gets a
use-site substitution. After freeze, each member root has a published view of
the same immutable component graph. All member views become visible before any
external incoming use is instantiated. This matches the Oracle scheduler
observations recorded in the ledger, without requiring a particular scheme
encoding.

## 3. Parent ports are not aliases

The operation under study is a boundary map, not variable equality. A candidate
port key is `(local vertex, polarized exposure)`; the polarity component is
provisional and exists to prevent silently merging lower/upper approximations.
For every selected exposure, intrusion allocates one boundary parent and
records a relation from the graph endpoint to that parent. Repeated references
to the same selected exposure reuse the same port. Distinct exposures may share
a parent only after a proof that their polarized constraints are equivalent.

An outer/rigid vertex remains an outer/rigid endpoint, with no local parent.
A local vertex with no boundary-relevant exposure remains component-local.
The closure criterion that selects ports is not yet proved: syntactic
reachability may over-generalize, while a criterion based only on root
occurrences may miss a bound reachable through a cycle.

The parent relation does not erase the original graph vertex or its edges. In
particular, `local == parent` is not an allowed interpretation: it would
identify identities and could reduce intrusion to level lowering without
establishing that the lower/upper approximations are preserved.

## 4. Instantiation uses overlays

An instantiated use receives a fresh overlay `sigma` for that use's local
boundary ports. All occurrences of one port in that use consult the same
overlay entry; another incoming use receives a disjoint overlay. Outer/rigid
endpoints resolve to their shared environment identities. The frozen component
graph is read-only during use instantiation.

Constraints produced by the use are attached to the overlay and its use-local
endpoints, not written into the frozen graph. Otherwise two uses can constrain
the same stored local vertex with incompatible choices and cease to be
independent. This is the current isolation invariant for the candidate model;
it still needs a formal preservation proof against the Oracle's use behavior.

Monomorphization may later choose concrete values for overlay ports and
specialize the frozen graph through the same lookup. It must preserve any
recursive edges and outer identities. This draft does not specify a cache key,
runtime representation, or serialization format.

## 5. Candidate correctness statement

For a finite frozen component `G`, enclosing environment `E`, member root `r`,
and incoming uses `u₁ … uₙ`, the intended theorem is:

1. each open internal reference resolves to the live SCC root and contributes
   the same constraints as the pre-freeze graph;
2. each external use is equivalent to solving one fresh copy of the
   boundary-relevant degrees of freedom of `G`, with every outer/rigid vertex
   shared through `E`;
3. the overlay solver returns a principal solution for that use, and constraints
   from `uᵢ` cannot change the solution space of `uⱼ` for `i != j` except through
   identities explicitly shared by `E`;
4. projecting any member root from the shared component gives the same
   observable type constraints as generalizing that member under the Oracle's
   SCC lifecycle;
5. cycles and shared descendants remain regular graph edges and do not require
   path duplication to state the result.

This statement is not yet a theorem: “equivalent”, “principal”, the exact
boundary-relevant port criterion, and the supported type constructor algebra
need definitions. It deliberately says nothing about matching F5 binder shape.

## 6. Required counterexamples and proof obligations

Before choosing a runtime representation, the proof must cover:

- a diamond with two paths to one local vertex, proving one port is shared;
- a local diamond ending at an outer rigid vertex, proving capture is avoided;
- a nested Function where the same vertex is exposed at both polarities;
- two incoming uses constrained differently, proving overlay disjointness;
- an SCC with an internal reference plus an external incoming use;
- productive nominal-guarded recursive Function bounds, retaining all cycles;
- an unproductive Function-only cycle, matching its observed collapse;
- different root-processing orders, proving alpha/order independence;
- failure during preparation, proving no member is partially published.

The first essential lemma is a lossless boundary factorization: every
constraint path from a local SCC vertex to an independently instantiable
exposure crosses exactly the selected boundary ports, while paths to outer/
rigid vertices remain anchored in `E`. The second is overlay isolation. The
third is principal solving for the chosen finite regular graph class. None has
been proved here.

## 7. Known gaps and next step

The Yulang2 audit found in-place level lowering in `extrude_pos` and
`extrude_neg`, not fresh parent allocation. Therefore this candidate cannot be
described as a proved optimization of that operation. It is a new semantics to
compare by observable behavior.

The Oracle source language probe for two mutually recursive local definitions
capturing one outer parameter failed on the forward local reference. That exact
topology therefore needs either a valid source construction or a synthetic
constraint-graph characterization with an explicit note that it is not a
source-level Oracle observation. Pure Function-only and nominal-guarded cycle
witnesses currently establish only their exact observed programs.

Next, define the polarized bound-graph denotation and solve relation precisely,
then work the listed examples by hand or with an independent finite model.
Implementation and production representation remain gated on a reviewed
successor contract and explicit approval.
