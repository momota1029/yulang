# Parametric component linking and the finite-program proof target

Date: 2026-10-02
Status: Draft; research theorem package; no implementation authority
Scope: finite graph substitution and joint relational linking; source summary construction remains open
Approved-by: none for a new source or acceptance rule
Drafted-by: primary with bounded architect audit
Reviewed-by: compiler_referee and spec_auditor; M3 package review and independent generic-arm scope delta review, no findings
Executable-linking-review: §7 independently reviewed by compiler_referee and spec_auditor, 2026-10-03; no blocking/major findings; minor translation-layer notation repaired by primary
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

Charter §20's hidden request `beta_local` is likewise distinct from logical
projection witnesses and solvable inference variables. `Req_p(rho)` binds
all dependent packet fields together; its elimination opens rigid `kappa`
under the declared bounds while the known family instance stays fixed.
Caller-private witness equations remain jointly retained, not assumptions
available to that arm proof. Pack/unpack cut transports the existing witness
without changing shared/captured scopes. Dependent result/store roots retain
that correspondence; this algebra proves no new escape restriction or source
lifecycle completeness.

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

## 7. Executable linking before safety saturation

This is a new successor construction using the user-selected Yulang call
and handler rules, not a Simple-sub-original extrusion theorem.

### Inputs and claim

Take finite generated **open** code/descriptor templates from computation-core
§§6 and 9, and a finite link/instance graph. Each instance supplies its
source-respecting shape, role, profile, typed-path and binder maps. Template
generation and those maps are premises: the construction does not infer
them from arbitrary source or prove their lifecycle admissibility.

Every reachable callable body, latent code provider and primitive routine
must occur in the linked graph, or be covered by a previously justified
driver with its stated interaction envelope. Merely naming an external
provider does not supply its code or justify arbitrary future interactions.
Retain the existing primitive, typed-flow, owner/view and store premises.
Unknown-shape adapters are not introduced as opaque executable nodes.

For these inputs, construct one finite linked code/descriptor graph, then
the concrete query/control kernel of source-realization §7 and its existing
finite heap abstraction. This closes a supplied merged-kernel premise for
contextual recertification with different finite supplied interactions.
It does not establish general Function subtyping, unknown-client coverage,
full source generation or principal source inference.

### Construct the linked executable graph

1. Allocate a namespace for each instance's owned code labels, descriptor
   nodes, local binders and source boundary/profile identities. Alpha-rename
   bound proof names while retaining rigid scopes and imports. Type-port
   maps may be noninjective where the supplied source map permits sharing;
   owned identities remain injectively renamed. Runtime heap addresses do
   not become static endpoint or binder identities.
2. Copy template adjacency and incidence entries once per supplied instance,
   grafting external endpoints and profile/path references through its map.
   Preserve back edges, shared imported roots and all joint `K,D` references.
   Do not unfold recursive code or regular descriptor graphs.
3. Wire each application to its actual callable descriptor and whole argument
   code. Higher-order calls still obtain their runtime callable and follow
   its retained descriptor; linking does not choose a unique static target.
   Argument construction remains an inert delay. Execution establishes
   the actual receiver and typed receipt before its actual entry program.
   Keep body execution, designated result consumers, separately admitted
   result adaptation and every native return delimiter in their original
   phase order. In particular, an operation's declaration-derived consumer
   follows native request-thunk return; it is not moved into entry or body.
4. Returned or stored latent handles retain their actual code/descriptor
   links, lexical references and typed paths. Later demand follows those
   links under the current context rather than replacing the handle by its
   outward row or historical maker activation.
5. Connect operation emission and handling through the full existential
   request packet of charter §20. The known family instance stays fixed;
   payload, raw continuation, dependent suffix, profiles/evidence and `K,D`
   share the retained local witness. Raw resume enters the saved suffix with
   that witness and current store, without reinstalling the selected shallow
   handler. Fresh proof names are correspondence names, not new instances.
6. Use one store, active context and evidence relation across the whole graph.
   Shared cells, aliases, owner links and continuation roots remain shared.
   There is no independently summarized heap per component and no join of
   previously computed component rows or safety certificates.

These steps are graph assembly, not a new source translation or execution
rule. They instantiate the original source contracts and retain all declared
checking bounds. Changing the supplied finite caller domain changes the
linked graph, not the callable's source annotation or generic arm discipline.

### Finite construction and query closure

Let `s_i` count instantiated template adjacency and incidence entries,
including labels, descriptor edges, binder/path maps and code successors;
let `ell` count link entries. With indexed namespace/map lookup, assembly
takes `O(sum_i s_i + ell)` graph work. Substituted endpoints are references
to graph roots, not recursively copied type trees. This bound is before
global query products and abstract saturation, not a linear bound on them.

Run source-realization §7 query lowering on this assembled graph. It expands
the existing typed-path/visibility/search routines into shared finite control,
with loops and recursive calls represented by back edges. Its finite
descriptor and query inventory is built from the linked graph's finite
static labels and admitted query signatures. The basis includes the grounded
products required by that construction; a later finite caller graph may
produce a different finite basis. No fixed inventory for all clients follows.

Type/family and scoped predicates retain their mathematical interpretations
under the same assignment. Queries outside the proved equality/row kernels
remain interpreted, unsolved predicates. Their finite occurrence inventory
does not supply an effective decision procedure or make unresolved checks
valid. Keep their original dependencies and checking scopes in `Base`.

Only after linking and query lowering apply the existing finite heap
abstraction and its joint state construction. Its existing finite bound
includes store/context/evidence products; the assembly bound does not bound
that product linearly. Retain dynamic event identities and the source owner
protocol as required by its simulation premises, separately from static
request-family endpoints.

### Translation/linking commutation and simulation

Let `D_i` be the resolved open derivations, `T_i = Translate(D_i)` their
generated templates, and `L` the supplied finite linking graph. Let
`D_L = Link_L(D_i)` use precisely those instances and source maps. Then,
up to consistent alpha-renaming,

```text
Link_L(T_i) = Translate(D_L).
```

Both sides use the same translation phases, templates, port maps and native
delimiters. This equation is conditional on the supplied resolved derivation;
it is not an instance-completeness theorem for arbitrary source elaboration.

**Proof.** Induct over translation nodes and their link incidences, treating
recursive back edges as shared references. Literal/name/descriptor creation
commutes with grafting because lookup reaches the same shared roots. Inert
delay and closure construction retain the same lexical and typed references
without running their code. Bind appends the same suffix using the ordinary
state-threaded relation, including each requesting prefix.

At a call, both constructions delay the complete argument, establish receipt
at the actual receiver, and run that producer's entry. A value entry forces
one designated computation view and rebinds its result; retained entry binds
the carrier. Neither construction forces latent descendants. Body/result
consumers run in the same order, and returns cross the same native delimiters.
This includes the operation's post-native-return declared consumer.

At explicit `Force`, both follow the same delayed code and typed path under
current state. At a request, pack/unpack proof substitution transports the
entire packet, not separately chosen payload/response witnesses. An alias
or store access reaches the same cell and corresponding dependent roots.
At raw resume, both use the current response/store and saved suffix with
the same witness and owner protocol; neither revives the selected handler.

Graph queries lower the same source profile/path relation. Ordered shallow
search therefore tests the same actual candidates; forwarding, selection,
outside guard/arm execution and raw resumption retain their source phases.
Symbolic predicates are interpreted at one shared assignment on both sides.
The existing primitive/query correctness premises cover their instruction
steps; unresolved source predicate solving is not proved by this induction.

It follows that every finite linked execution prefix is simulated by the
constructed concrete kernel, with latent future demand and repeated raw
resumption included under the supplied interaction envelope. Applying the
existing heap/control simulation maps every such prefix to the generated
abstract kernel. Every actual nondeterministic successor is covered: the
construction cannot select only a compatible response, store realization or
successful search case. Abstract extra successors remain subject to the
existing conservative judgment; reverse exactness for that abstraction is
not claimed here.

### Recompute the joint certificate after linking

For the resulting finite abstract state set `Q_link`, use its generated
initialization, guards, designated faults and complete output alternatives:

```text
R_link,i = I_link,i or OR_j (R_link,j and G_link,ji)   [least fixed point]
S_link   = Base_link and not OR_i (R_link,i and Bad_link,i)
U_link(w)= S_link and OR_i (R_link,i and Out_link,i(w)).
```

Generic-arm uniform checking remains in `Base_link`, distinct from reached
request-instance obligations in the kernel. All-Int actual calls cannot
validate an arm that narrows its rigid local binder. Pack/unpack cut uses
an already checked uniform proof; reachability does not manufacture one.
Retain original contracts when altering the supplied finite caller domain.

With the fixed finite Boolean inventory, reachability stabilizes within
`|Q_link|` synchronous rounds: every reachable state valuation has a simple
path of length less than `|Q_link|`. The existing certificate theorem then
gives the principal result **only for its abstract certificate judgment**.
It does not prove exact concrete acceptance or principal source schemes.
The designated-fault reflection and primitive/store premises remain required.

Recomputing `R_link,S_link,U_link` uses one joint linked relation. Joining
component `S` values or outward rows instead would omit shared interactions
and does not satisfy this theorem. An outward row remains a projection of
the joint `U_link`, with `S_link` and dependent packet incidence retained.

### Economy and remaining gates

This route reuses the source relational execution and existing `R/S/U`
certificate construction after concrete linking. An alternating simulation
comparison would introduce a different comparison judgment and proof
obligation; it is not selected by this construction. No supported source
acceptance is narrowed to obtain finiteness.

Milestone 3 still requires generation of the admitted open templates/maps,
effective complete checking predicates and the source soundness/principal
denotation bridge. This section removes the supplied merged executable
kernel premise within its finite resolved input envelope, not those gates.
Milestone 4 must then derive legal generalization/freshening/SCC instance
graphs and preserve binder ownership and dependent lifecycle. Milestone 5
addresses implementation feasibility; Milestone 6 requires approval before
compiler implementation. Unknown clients and general Function comparison
remain outside this finite supplied-interaction theorem.
