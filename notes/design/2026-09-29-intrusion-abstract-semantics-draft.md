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

An edge occurrence records a polarized type endpoint, its direction, stable
source/proof identity, and any weight annotation. An endpoint is a constant, a
constructor applied to endpoints, a Function of endpoints, or a reference to a
type vertex. A lower edge records `endpoint <: vertex`; an upper edge records
`vertex <: endpoint`. Which lower occurrences are eligible for a scheme root
is a separate evidence-sensitive projection decision; it is not implied by
mere presence in the structural bound graph. This draft assumes bound closure
reaches a fixed point before the graph is frozen.

### Oracle closure relation for the fragment

The Oracle's constraint entry takes a positive endpoint `p` and a negative
endpoint `n`, and records the obligation `p <: n`. In the variable-only cases,
the audited closure rules are:

```text
Var(v)+ <: Var(w)-, v != w:
    add Var(v)+ to lower(w)
    add Var(w)- to upper(v)

Var(v)+ <: n, n not Var:
    add n to upper(v)

p, p not Var <: Var(w)-:
    add p to lower(w)

Var(v)+ <: Var(v)-:
    no new bound
```

Bounds are installed before propagation continues. Structural constraints add
subtype obligations until the worklist reaches its fixed point. For pure
Functions, `Fun⁺(a⁻, r⁺) <: Fun⁻(a⁺, r⁻)` adds `a⁺ <: a⁻` and `r⁺ <: r⁻`;
the argument obligation reverses direction and the result obligation keeps it.
For the finite core used here, `Bottom <: n` and `p <: Top` close immediately;
`(p₁ ∪ p₂) <: n` adds both branch obligations; `p <: (n₁ ∩ n₂)` adds both
upper-branch obligations; and equal nominal constructor heads add the
declared invariant argument obligations. Mismatched nominal heads and all
effect/row cases are excluded from this first graph class.
This records the Oracle's operational constraint relation for the fragment,
not a denotational model of all possible runtime types. The source audit and
the SCC scheduling observations are recorded in the behavior ledger.

The candidate intrusion proof must show that parent/overlay construction
preserves this closure relation after projecting each component root. It must
not replace the two variable-bound insertions with an equality edge merely
because both mention the same graph vertices.

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

The operation under study is a boundary map, not variable equality. The
candidate parent map is `P: selected local TypeVar -> boundary TypeVar`, with
one parent per selected local vertex, independent of whether an occurrence is
positive, negative, or both. This is necessary to retain one type identity for
a variable used in both Function argument and result positions, as in the
Oracle's identity Function.

Intrusion transports lower and upper edges separately through `P`. Every
selected local endpoint is renamed by the same map; every outer/rigid endpoint
keeps its existing identity. A local variable not selected by `P` remains
component-local. Distinct local vertices get distinct parents unless a separate
quotient proof justifies merging them. Polarity belongs to each transported
edge and to later root projection; it does not create a second parent for one
TypeVar.

This full-interval transport is a candidate, not an established equivalence.
The key lemma must show that preserving both bound directions on the parent
graph does not add constraints where Oracle generalization would retain only a
positive or negative approximation, or eliminate a one-sided variable. If it
fails, the design must refine the parent relation and explain how it still
retains shared identity for bipolar variables.

An outer/rigid vertex remains an outer/rigid endpoint, with no local parent.
A local vertex with no boundary-relevant exposure remains component-local.
The closure criterion that selects ports is not yet proved: syntactic
reachability may over-generalize, while a criterion based only on root
occurrences may miss a bound reachable through a cycle.

The parent relation does not erase the original graph vertex or its edges. In
particular, `local == parent` is not an allowed interpretation: it would
identify identities and could reduce intrusion to level lowering without
establishing that the lower/upper approximations are preserved.

### Edge-transport lemma for an injective parent map

Let `rho` rename every selected local variable to a fresh parent, leave all
other variables fixed, and map every type-expression node homomorphically while
memoizing node identities. Require parent IDs to be fresh and pairwise
distinct. Transport both lower and upper edge sets by `rho`; do not delete the
original frozen graph. Let `C(S)` be the least closure of a finite set `S` of
subtype obligations under the fragment's variable, Function, union,
intersection, and same-head invariant-constructor rules.

**Claim.** `C(rho(S)) = rho(C(S))`.

**Proof sketch.** Every closure rule is local to its endpoint constructors and
variable IDs. `rho` preserves constructors, polarity, and variable equality;
freshness prevents a renamed local variable from colliding with an outer or
rigid variable. Therefore each rule step `S -> S'` maps to the same rule step
`rho(S) -> rho(S')`. Conversely, `rho` is injective on the renamed graph, so
each rule step in the image has a unique preimage. Induction over finite closure
steps gives equality of the two closures. The fast path for
`Var(v)+ <: Var(v)-` is preserved because injectivity preserves exactly which
endpoints are the same variable.

This proves that alpha-renaming the bound graph to fresh parents neither loses
nor adds closure edges. It does **not** prove that the selected parent set is
the Oracle's generalizable set, that root projection is principal, or that
retaining both bound directions matches one-sided Oracle approximations. Those
are separate lemmas and remain the central semantic risks.

An executable characterization of this lemma lives at
`notes/progress/2026-09-29-intrusion-finite-model.py`. Running
`python3 notes/progress/2026-09-29-intrusion-finite-model.py` checks closure
commutation for identity sharing, directed variable flow, Function polarity,
invariant constructors, a shared diamond, an outer endpoint, and a nominal
recursive edge. It also checks that a non-injective quotient loses a directed
edge and that two separate overlays keep their rows separate. This script
implements the rules above; it is a regression aid for the proof sketch, not an
independent proof or a model of principal root projection. It also checks
one-sided erasure, matching lower/upper expansion, root-local polarity, and
positive-only recursive collapse. It does not encode the Oracle's recursive
binder table or prove principality.

### Candidate root-local polarity projection

The Oracle source gives a concrete projection behavior to model. For each
member root separately, it starts at positive polarity. A variable side is
expanded through lower bounds when positive and upper bounds when negative;
recursive visits are detected by `(TypeVar, polarity)` and represented by a
back-reference plus its recursive bound. Function arguments flip polarity and
results preserve it; unions are positive joins and intersections are negative
meets. After that root's reachable regular graph is built, the Oracle collects
variable polarity over the root and recursive bounds. A generalizable variable
seen at only one polarity is erased to that polarity's extreme (`Bottom` when
positive, `Top` when negative); a variable seen at both polarities remains
shared. Boundary/non-generic variables are excluded from this erasure.

The intrusion candidate must run this projection per member root over an
immutable shared component graph. Polarity census for one root must not absorb
occurrences belonging only to another SCC member: the Oracle produces one
generalized result per member, even though the component is solved together.
The internal result may remain a regular graph with parent references; it need
not copy the Oracle's closed scheme encoding. The semantic obligations are to
preserve the root-local reachability, recursive back-references, one-sided
extremes, and shared identity of bipolar variables. The finite model exercises
this rule on identity, constant-function, positive-bound, negative-bound, two
root-local views sharing a variable, and recursive Function witnesses. It
reproduces the structural results `'a -> 'a`, `any -> int`, and
`any -> any -> never` for the recorded identity, constant, and pure recursive
lambda graphs. It does not encode the Oracle's recursive-binder table or prove
principality.

### Alpha-renaming commutes with the pure root projection

Here `Project` means `compact_root_for_scheme` graph collection followed by the
polarity census and one-sided-variable elimination described above. It does
not include the Oracle's other simplification passes such as coalescing,
pinned-interval collapse, sandwiching, or role processing.

The audited Oracle projection path provides a stronger lemma for the first
pure graph fragment. Let `G` be the already scope-filtered, frozen lower/upper
graph for one generalization boundary; this lemma does not prove that
`scheme_projectable_lowers_in_scope` selects the right edges. Let `rho` be an
injective renaming from selected local variable IDs to fresh parent IDs. Assume
it preserves each variable's generalization-candidate predicate
(`level >= boundary && !non_generic`), maps the selected root, and renames
every edge occurrence in `G` without changing its direction, constructor,
weight, stable source record/evidence, or iteration order. The already selected
edge occurrences and their order are part of this lemma's input: the Oracle
collector processes lower-bound records in order, and recursive-side bounds
are stored by `(TypeVar, polarity)` even though cache keys also include weight.
`rho` is the identity on outer/environment variables.
Then the Oracle root projection commutes with `rho`, up to alpha-equivalence
of recursive-side ordering:

```text
Project(rho(G), rho(root), rho(environment))
    = alpha(rho(Project(G, root, environment)))
```

Reason: the collector cache is keyed by `(TypeVar, polarity, weight)`, while
recursive re-entry and the recursive-side set are keyed by `(TypeVar,
polarity)`. Injectivity preserves equality and inequality of variable IDs in
both key spaces; keeping annotations, source record decisions, and iteration
order fixed maps every structural descent to the same polarity descent and
preserves which weighted visit records each recursive side. Thus cache hits,
recursive re-entries, and recursive-side membership commute with renaming,
and the root and recursive-side table are renamed homomorphically. The
following polarity census also commutes with renaming. Finally, its
elimination predicate is `level >= boundary && !non_generic`, so preserving
that predicate preserves exactly which occurrences are eligible; one-sided
versus bipolar status is unchanged. Recursive-side serialization order may
differ because the Oracle sorts by numeric TypeVar ID, which alpha-equivalence
deliberately ignores.

The implementation evidence is
`compact/collect/mod.rs::compact_root_for_scheme,compact_var_side` and
`compact/analysis/mod.rs::eliminate_polar_variables_with_roles_and_non_generic,
is_simplification_candidate` in the frozen Oracle at `a58eefc3`. This lemma
supports preallocating injective parents before visiting roots in any order,
provided parent metadata preserves the candidate predicate and the frozen edge
selection is already correct. It proves renaming invariance for projection,
not edge selection, the parent set, instantiation overlays, SCC scheduler
equivalence, or principality.

### Oracle lower-edge selection is evidence-carrying

The frozen Oracle does not project every structural lower-bound record
unconditionally. In scheme mode, `compact_var_bounds` asks
`scheme_projectable_lowers_in_scope` for each variable's lower records. That
query preserves an unclaimed record, discards a record whose `project_lower`
decision is `Excluded`, and keeps an `Included` record with support/evidence
metadata. Missing or inconsistent proof state is a fallible projection error,
not an implicit inclusion.

Consequently an intrusive graph cannot model the full Oracle boundary as only
`(owner, direction, endpoint, weight)`. The selected edge occurrence also has
source record/proof identity. Some proof carriers refer to constraints, replay
derivations, claims, and type-variable pivots. There are three possible
transport designs to prove: transport and validate these references together
with type endpoints; select and validate edges on the original graph at the
component freeze, then reuse the selected ordered edges without re-querying
after renaming; or define replacement-owned evidence that makes the same
include/exclude decision. The second route depends on showing selection occurs
at the correct boundary and that the selected edges remain valid until every
member root view is built. The collector consumes the selected bounds after
the query and does not inspect their reason/evidence payload during structural
collection. Thus copying only final structural edges is justified only after
the selection decision is frozen with them. The Oracle entry
`compact_type_var_for_scheme` creates a fresh projection-evaluation round and
scoped query for each requested root, so a preselection cache shared across
member roots must also prove that it preserves those per-root decisions and
failure behavior. Otherwise the selected-edge mask itself must remain
root-local.

This adds a separate proof obligation before claiming ordinary Oracle
capability: characterize when lower records are Unclaimed, Included, or
Excluded in the supported pure input envelope, then show a selected-edge
transport design preserves that decision and its failure behavior. Restricting
the first envelope to unclaimed pure edges is a possible research boundary,
but it is not chosen here; it would need source-level coverage and an explicit
compatibility limit before implementation. Source locators at `a58eefc3`:
`constraints/structural_kernel/access.rs::scheme_projectable_lowers_in_scope`,
`compact/collect/mod.rs::compact_var_bounds`, and
`constraints/proof/mod.rs::project_lower_inner`; the per-root projection round
is created by `compact/surface.rs::compact_type_var_for_scheme`. Proof payload
types are in `constraints/mod.rs` and `constraints/proof/mod.rs`.

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

For the first graph comparison, “same observable constraints” means that after
applying each use overlay and closing subtype obligations, the positive and
negative bound reachability at that use and at every shared outer vertex is
isomorphic up to fresh internal vertex renaming. Agreement only after rendering
a formatted scheme is too weak: it could hide lost edges, merged independent
uses, or captured outer identity. This graph isomorphism is a proof aid, not a
proposed public scheme contract.

## 6. Required counterexamples and proof obligations

Before choosing a runtime representation, the proof must cover:

- a diamond with two paths to one local vertex, proving one port is shared;
- a local diamond ending at an outer rigid vertex, proving capture is avoided;
- a nested Function where the same vertex is exposed at both polarities,
  proving one parent identity while retaining both directional edge sets;
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

### Worked closure facts

**Identity root.** The body graph contains one `Function⁺` node whose argument
references `a` negatively and result references the same `a` positively. Its
lower edge into the definition root preserves this exact sharing. The Oracle
accepts `pub id x = x`; its two observed incoming uses produce `int` and a
Function result independently. This checks an acyclic boundary with one
bipolar vertex, but does not establish parent selection for recursive graphs.

**One-sided parameter.** The Oracle accepts `pub k x = 1` with scheme
`any -> int` and no quantified or recursive binders. Thus parent graph closure
alone cannot be the per-root result: the negative-only argument variable must
be projected away. The intrusion design needs a root projection that preserves
the component graph for other roots while eliminating this member's
one-sided exposure.

**Directed variable flow.** For `a⁺ <: b⁻`, closure stores `a⁺` in `lower(b)`
and `b⁻` in `upper(a)`. It does not assert `a = b`. A candidate that maps both
vertices to one parent would turn these obligations into self-edges and erase
the distinction. Unless a separate theorem justifies that quotient, the safe
candidate retains distinct ports and both directed bounds.

**Use separation.** Two identity uses create overlays `sigma₁` and `sigma₂`.
The observed Oracle program instantiates one at `int` and one at a Function
type. If both overlays wrote into one mutable component graph, either choice
could constrain the other use. The immutable graph plus disjoint overlays
avoids that direct mutation, but a proof must still show propagation cannot
escape from one overlay through a shared outer endpoint except where the
enclosing environment intentionally shares it.

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
