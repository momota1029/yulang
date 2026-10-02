# Parametric component linking and the finite-program proof target

Date: 2026-10-02
Status: Draft; research theorem package; no implementation authority
Scope: finite graph substitution and joint relational linking; source summary construction remains open
Approved-by: none for a new source or acceptance rule
Drafted-by: primary with bounded architect audit
Reviewed-by: compiler_referee and spec_auditor; M3 package review and independent generic-arm scope delta review, no findings
Supersedes: uniform grounded client coverage as a mandatory proof prerequisite, not any source rule

## 1. Correct the quantifiers before enlarging the analysis

Charter §12 asks for finite principal presentations per finite source program.
It does not require one fixed grounded endpoint/predicate inventory to contain
every future client's instances. Distinguish:

```text
for every finite linked program P, there exists a finite presentation G_P

there exists one fixed grounded inventory Omega_C for component C,
    covering every admissible future client L without extending Omega_C.
```

The second is stronger. The heap-backed client-driver theorem proves useful
coverage under a template-closed signature, but deriving that uniformly
grounded signature is one possible route, not a necessary intermediate goal.
It remains available if a later theorem needs it.

The proposed shorter route keeps a finite **parameterized constraint graph**
for a component, links it to finite use-site graphs, and constructs the
grounded query inventory for the resulting finite program. This is compatible
with preserving an SCC graph as the generalized authority. It is not yet a
proof that such principal summaries can be generated from source.

The endpoint objection is concrete. Consider the schematic declaration
`op : forall a. a -> Unit` in a parameterless family. One finite client may
use it at arbitrarily many pairwise distinct local instances while exposing
only that family and a Unit result. The operation-instance package requires
those local maps to remain distinct wherever their dependencies remain live.
A fixed finite set of endpoint names under one assignment cannot literally
name arbitrarily many distinct types at once. Increasing the number of
client sites gives another finite program, not an infinite source program.
This refutes that literal fixed-inventory encoding as a universal premise;
it does not refute a finite quantified schema, a richer quotient, or source
principality. It is a schematic representation witness, not an Oracle
acceptance claim.

## 2. Finite graph grafting without type-identity erasure

Let a template `G` be a finite graph with constructor, constraint, profile,
typed-path and incidence nodes. Named external ports are `X`; owned local
names are `Z`. Edges may form cycles. Each primitive constraint node has a
finite operand list with a specified meaning; naming an undecided relation
does not make it an effective primitive.

A finite substitution map sends external type ports to roots of finite
descriptor graphs `D`. Allocate fresh local names for this copy, then graft
the external references to their target roots. Copy each template node and
adjacency entry once; preserve all back edges. Multiple occurrences of the
same port use the same target. Grafting does not unfold the target graph.

Type-port substitution may identify two external type ports. This does not
permit identifying distinct source boundary binders, annotation occurrences,
dynamic events or owners. Their fresh-name transport is injective where
ownership requires distinct identities, and fixes shared imports. Profile
paths, operation maps and `K,D` references undergo their corresponding
consistent transport; type equality alone creates no capture grant.

For a supplied finite instance graph `I`, make one template copy per distinct
instance vertex and wire recursive edges to already allocated copies. Its
representation size is bounded by

```text
|D| + sum_{i in I} |G_i| + number of linking/map entries,
```

where sizes count nodes and adjacency/incidence entries. With indexed maps,
construction uses the same order of graph work. A cycle in `I` is a back edge,
not a request to generate an infinite sequence of new instances.

This proves finiteness for any supplied finite instance graph, including
arbitrary finite client descriptor additions. It does **not** prove that
source polymorphic recursion, use-site freshening or shape-dependent
elaboration generates a finite `I`. Finite syntax alone is insufficient for
that claim. Selecting which recursive edges share an instance is a lifecycle
obligation, not an implementation shortcut justified by this bound.

**Substitution lemma.** Interpret the grafted graph under one assignment
`nu`. Interpreting an original external port `x` by the interpretation of its
grafted target gives the same interpretation to every corresponding node and
constraint. For ordinary constructors, follow their operand edges; for a
primitive relation, its entire operand tuple is transported together. For
cyclic equations, corresponding assignments satisfy exactly the same
simultaneous equations. If a declared monotone recursive relation has a
least/greatest interpretation, the corresponding operators agree under the
renaming, so their designated fixed points agree. No unproved recursive
meaning is supplied merely by drawing a cycle.

Thus further substitution composes with grafting, up to local alpha-renaming.
The operation-instance identity `sigma(Sigma theta) = Sigma(sigma o theta)`
is one instance. The same proof transports profile/dependency references;
it does not remove a selected-family constraint when its effect leaves the
outward row. No source execution, force, adapter or fresh dynamic event is
introduced by graph substitution.

## 3. Joint linking and exact projection

The algebraic law below identifies what a reusable summary must preserve.
It does not choose which source binders may be generalized.

Write a component constraint relation as `F_i(X_i,Z_i)`, where `X_i` contains
**all** externally shared interface and dependency coordinates. These include
relevant store/alias, context, continuation and typed-view coordinates when
the relation uses them; `X_i` is not merely the outward effect row. `Z_i`
are existential local witnesses of this logical presentation. Logical hiding
is distinct from source let-generalization or freshening a mutable value.

In particular, the rigid operation-local arm binders `kappa` of charter §19
are bound checking parameters, not existential local witnesses `Z_i`.
Preserve their binder scope and declaration bounds in the graph and summary;
captured endpoints remain shared. For example, a scoped relation may have
`exists Z_shared. forall kappa_arm. exists Z_body. K`: arm-local typing
witnesses may legitimately lie inside the rigid checking scope. The linking
algebra supplies no permission to move already shared/captured `Z_shared`
from `exists Z_shared. forall kappa` to `forall kappa. exists Z_shared`, or
to replace rigid `kappa` by a solvable existential from caller instances.
Source construction and completeness of this uniformly checked arm
presentation remain separate proof obligations.

At each linked instance choose an admissible external type substitution
`sigma_i` and the required identity transport. Alpha-rename the genuinely
local `Z_i` to be pairwise disjoint and absent from all other relations and
the client constraint `H`. Leave all shared imports and dependencies shared.
Let `F_i^sigma` denote this consistently transported relation. Then:

```text
exists Z_1,...,Z_n. (H and conjunction_i F_i^sigma)
    = H and conjunction_i (exists Z_i. F_i^sigma).
```

Equality is pointwise on the **same joint external assignment**. Left to
right restricts the joint witness to each disjoint block. Right to left
combines the witnesses; disjointness and absence from `H` and the other
relations ensure that no two choices assign the same hidden coordinate.
External substitutions may be noninjective on type ports: their repeated
targets are already fixed by the common assignment on both sides. They
cannot capture a local witness because local renaming precedes substitution.

The exact summary is therefore `S_i(X_i) = exists Z_i. F_i(X_i,Z_i)`.
Replacing a component relation by this summary before conjunction preserves
the joint solution relation precisely under the stated separation premises.
Any further joint projection to public/use-site roots also agrees. For a
chosen representable constraint language ordered by solution inclusion, exact
representations of these equal relations have the same principal denotation.
This is an algebraic preservation theorem, not existence of a representable
principal summary for arbitrary source.

Retaining the internal graph and its binder table can represent this logical
projection without expanding or deleting `Z_i`. But a finite expression
`exists Z. F` alone proves neither effective solving nor closure in the chosen
scheme language. Source instance completeness, effective constraints and
principal projection still have to be established.

### Why shared witnesses cannot be treated as local

Let `k` be a shared witness with distinct admissible values Int and Bool.
The joint relation `(k = Int) and (k = Bool)` has no solution. Separately
hiding a fresh `k` in each conjunct makes both conjuncts satisfiable. This is
exactly the forbidden situation when a value, operation instance, store cell
or resumption still shares the witness across uses.

Such a coordinate must remain in the shared interface, or be bound once
around the whole joint relation. `D` is part of the evidence needed to detect
this dependency; it cannot be recomputed from materialized family equality.
This law gives no permission to treat every source-local name as an
independently fresh scheme binder.

## 4. Do not confuse summary substitution with certificate reuse

The finite safety-certificate theorem computes its maximal safe assignment
domain for a particular transition graph and admissible interaction domain.
A closed result for one client is not a constraint summary for every client.

For example, a receiver that calls a pure callback may have a pure complete
call. Widening its input domain to admit a callback exposing `E`, while
keeping that pure result certificate, is the existing core §8 counterexample.
Transporting the certificate's syntax does not add the previously absent
interaction. Likewise, independently projecting hidden store/control state
on each transition can combine incompatible witnesses across a path. The
joint projection law applies to a complete relation under separation, not
to replacing every edge with its marginal relation and then saturating.

The shorter route therefore retains an **open constraint summary** whose
interaction ports and dependencies are linked before the program's safety
closure is computed. It may reuse a closed certificate only under a proved
domain-preservation/composition theorem, such as the narrowly scoped core §8
case. Merely keeping source code and rerunning its elaborator at every use
does not prove reusable principal scheme inference.

Required instance completeness is the following equality, at common roots
and under one assignment:

```text
Solutions(linked summary constraints) projected to public/use-site roots
  = Solutions(linked component constraints) projected to those roots.
```

The substitution and joint-link laws prove the algebra once the summary's
complete relation and binder separation are supplied. They do not show that
source generation emits that complete relation, that `OpCompat` has effective
finite constraints, or that the component has no hidden context dependency.

## 5. Why descriptor heaps alone do not close symbolic inference

A finite vocabulary of linked record constructors can encode arbitrary
finite type, operation, profile and formula graphs. This is a useful
representation fact. Applying a finite allocation-site abstraction to those
records must not identify their symbolic binders.

Two local maps for the same parameterless operation can use independent
endpoints `a=Int` and `b=Bool`. If both endpoint records map to the same
abstract allocation address, interpreting that address as a single type
variable falsely replaces their consistent joint assignment by
`v=Int and v=Bool`. Treating equality of the addresses as equality of the
instances can instead invent compatibility. Choosing a new interpretation
on every read loses the persistent instance correspondence.

Consequently finite record tags or machine control do not imply a finite
symbolic predicate inventory. The per-program route keeps static endpoint
and binder identities distinct from abstract runtime addresses, constructs
the program-specific finite descriptor/query graph, and only then applies
the reviewed runtime heap abstraction. Its missing construction is now
localized to finite source summaries and finite linking, rather than an
unbounded population of runtime handles. This is a failure of a naive
encoding, not a class-3 non-finiteness result.

## 6. Revised milestone exit and next proof

Use the following source presentation gate:

1. Generate a finite open constraint/descriptor template for the ordinary
   source component, with all complete invocation ports and `K,D` exposed.
   Supply effective query/command meanings rather than an opaque inclusion
   or compatibility leaf. Constructor/role inference remains part of this.
2. Establish its instance completeness and finite query closure for finite
   linked instance graphs, using the substitution and joint-link laws above.
   The chosen conservative judgment still needs its source soundness and
   principal-denotation bridge; possible extra rejections require the
   existing compatibility treatment.
3. In Milestone 4, prove that source generalization, independent incoming
   uses and internal SCC uses produce precisely the permitted instance
   graphs and preserve binder ownership/separation. Prove intrusion there;
   do not assume this lifecycle result to certify the full source system.

This is a proof-order correction under the existing target, not a new
language restriction, implementation plan approval or claim that a uniform
client driver is impossible. It keeps scheme reuse as a real obligation.
It does not close Milestone 3 or 4, approve a source acceptance loss, or
open the later method/role or implementation gates. The next concrete task
is source constraint-template generation and its instance-completeness
proof, using complete producer execution rather than body-result rows.
