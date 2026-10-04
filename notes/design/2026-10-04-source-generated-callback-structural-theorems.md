# Source-generated hypotheses for the callback and structural conjectures

Date: 2026-10-04
Status: Reviewed conditional theorem package
Scope: two conditional mathematical theorems, with explicit source-generation tests
Base: `research/simple-sub-intrusion` at `9c2710e3`
Concurrent evidence integrated: through `e031208d`, including the segment-bound transport objection and the source-graph/finite-endpoint distinction
Implementation authority: none
Supersedes: none
Reviewed-by: independent compiler_referee per theorem and independent source/authority spec_auditor; structural minor clarification incorporated; callback transport major repair closed by a fresh independent compiler_referee delta review, 2026-10-04

## 1. Question, authority, and exact claims

The current user request permits additional hypotheses provided that they are
source-generated. This note uses that permission to specify constructive,
source-checkable hypotheses. It does not assume either desired conclusion,
select a compiler rejection policy, or assert that current inferred endpoints
already satisfy a generator that the repository has not implemented.

The two original gaps are recorded in
[direct main-gate attacks](../progress/2026-10-04-direct-main-gate-attacks.md):

1. **Callback:** source execution coverage `Sem <= P_actual` does not prove
   complete-bound containment `P_actual <= P_checked`. The missing step is
   inversion of the synthesized endpoint, together with query-independent
   challenge admission.
2. **Structural:** a finite residual ledger does not prove that every
   satisfiable shifted-descriptor/variance package has a regular model.
   Unrestricted finite-model reflection remains open.

Here the additional hypotheses concern a source generator and its finite
output. The callback generator retains the derivation of its entire bound;
the structural generator exposes a checkable condition on the incidence of
unknown source endpoints and their constructor requirements. Neither
hypothesis is "the desired inclusion holds" or "a regular model exists."

The governing source decisions remain
[callback context delivery](2026-10-03-callback-context-delivery.md),
[typed core §§3, 6, 9](2026-10-02-typed-computation-core-elaboration.md), and
[the redesign charter](2026-09-29-scc-intrusion-redesign-charter.md):
literal generation B; actual Pure/Handler introduction and syntax-derived
entry; inert whole arguments; distinct receipts; one assignment and joint
`K,D`; the selected `d-`, `d+`, `b+` occurrences; ordinary endpoint-dependent
queries. These hypotheses do not equate expected and synthesized endpoints.

### Reading the results

- Theorem C proves the intended **source-generated linked Pure-value lift**,
  including full conservative bounds, on an explicitly described source core.
  It does not cover an unrelated annotated callback merely because its
  printed ports resemble the linked schema.
- Theorem S proves regular completion and a terminating existence procedure
  for a source-checkable family that includes recursive open descriptors,
  Function contravariance, mandatory Record width, and multiple constraints.
  It does not settle the unrestricted structural finite-model conjecture.
- Both generators below are mathematical constructions. Their correspondence
  with every raw Yulang construct, general scheme instantiation, and the
  production inference implementation are separate obligations.

## 2. Callback: the constructive source hypothesis

### 2.1 Source core and fixed input

Use the derivation constructors of typed-core §2:

```text
d ::= literal | name | lambda(P,c) | operation(decl) | reify(c)
c ::= result(d) | eliminate_p(d) | call(c_f,c_a) | bind(x,c_1,c_2)
```

This is proof notation, not new user syntax. For this theorem the finite
linked derivation graph is monomorphic at recursive references. Each source
label and lexical binder is allocated before its children are visited;
recursion refers to an existing label. Finite separate client graphs can be
attached at source use sites. There is no requirement for one fixed grounded
inventory to cover all future clients.

Every callable, delay, operation routine, and designated result consumer that
the linked derivation can expose has such a source label. Immutable records,
aliases, and captures retain their original lexical roots. There are no
mutable-cell operations, opaque semantic imports, implicit adapters, or
handler-image nodes inside the offered argument/body/result/latent-provider
subgraphs. The actual invocation may run inside an independently supplied
source-typed ambient handler/owner context. Those ambient protocols remain
the same in both descriptions.

The already specified decorated owner/view kernel supplies activation,
typed paths, pending suffixes, raw resumptions, return delimiters, and
pre-dispatch observation. Its source witnesses are inputs before the tested
query. This theorem derives endpoint generation from a decorated derivation;
it does not silently claim to derive all decorations from raw syntax.

### 2.2 Local primitive bounds

Each primitive source instruction has its complete local relation, on all of
its operands and results. Exact source primitive relations are sufficient.
A conservative relation may instead be used at a primitive if its independent
source contract certifies the result types and preserves source labels,
operation instances, owners, paths, and all joint dependency operands.
For example, a scalar primitive can admit several values of its result type.
It cannot manufacture a handler, receipt, typed path, or capture grant.

The actual and checked constructions reference the **same local relation**.
Any local abstraction witness is retained with that instruction, before the
surrounding relational composition. There is no independent root widening.
The proof is conditional on the ordinary local primitive certificates, not
on a certificate for the Function query being proved.

### 2.3 Generator clauses

Define `G` by translating the source derivation, with the existing relational
images in `Rel_C`. All graph notation in this section is proof bookkeeping,
not an additional runtime carrier or solver primitive.

| Source node | Generated complete relation |
|---|---|
| literal / primitive | its local source relation |
| name | lookup of the same lexical root |
| lambda | source closure label, actual entry, body label, captured roots |
| operation | declared native producer followed by its designated consumer |
| reify | inert delay referencing the source computation |
| result | return the generated data descriptor |
| eliminate | execute exactly the identified one-layer computation port |
| bind | first child, typed result rebind, then the referenced suffix |
| call | callee, inert whole argument, actual invocation and receipt, entry, body, designated result consumer |

In particular sequencing uses the existing equations, with current decorated
configuration `C`:

```text
Return(v,C) >>= S
    = S(v,C)
Request(q,C,k) >>= S
    = Request(q,C, lambda(response,C'). k(response,C') >>= S)
```

The second clause preserves the original request and attaches the pending
suffix to its continuation. Resuming does not replay argument receipt or
freshen the operation-local type witness. The operation case retains the
native return delimiter before its declaration-derived result consumer.

A Value-entry closure is generated as:

```text
actual receiver and receipt;
within the complete invocation view:
    Force_argument(t);
    typed rebind to Value(a);
    actual body and designated result consumer;
    return from this invocation
```

The slot's selected static correspondences are generated before comparison:

```text
d- : whole argument carrier / designated Force view
d+ : argument-origin contribution at the complete CallView
b+ : body / designated-result-consumer contribution at J_call
```

These three occurrences stay distinct; `d-` and `d+` share a coordinate but
not an occurrence identity. Callback-value receipt and inner argument
receipt also remain distinct. The correspondences are the locations already
selected in the [value-entry record](../progress/2026-10-04-value-entry-bind-projection.md),
under "Authority adjudication," not consequences inferred from query success.

### 2.4 Complete bound denotation and logical witnesses

The bound of a generated root consists of all complete decorated observations
derived by its generated relation graph: finite prefixes, requests,
returns, all legal finite response/resumption histories, and finite future
uses of latent source descriptors. A closure or delay retains its source
label, lexical roots, and generated future interface after it is returned.
Recursive future use unfolds that label when the next interaction occurs.

Use exact joint logical hiding:

```text
P_G(X) = exists Z. F_G(X,Z).
```

`F_G` is the generated conjunction/composition at one external assignment.
Only genuinely local logical witnesses belong to `Z`. A shared local is
bound once around the entire relation; shared imports, lexical roots,
source-owned identities, and live `K,D` coordinates are never hidden
independently per segment. Rigid operation binders retain their original
quantifier scope. This is the existing linking law, not a fresh quantifier
exchange; see [parametric linking §3](2026-10-02-parametric-component-linking.md).

There is **no constructor** adding an arbitrary complete observation after
this projection. This is the additional source-generation discipline.
Auditing a generated graph checks constructor tags, operand/source maps,
local primitive certificates, sharing, and the absence of such an edge.
It never tests the desired whole-bound containment.

The allowed relational constructors are positive in their child behavior
relations: whole-tuple primitive leaves, conjunction with a fixed source
predicate, same-fiber conjunction/union, consistently renamed variables,
existential hiding at its original scope, and the sequencing/call images in
§2.3. A source binder keeps its fixed quantifier position; a guarded recursive
reference uses the least relation generated by finite observation
derivations, with finite prefixes included. Latent source descriptors retain
their labels, and their future interface is specified by all finite
developments from those labels. No unmentioned greatest-fixed-point or
liveness interpretation is selected. There is no
complement, test of non-membership in a child bound, or conditional choice
based on the success of the tested Function inequality. A handler dispatch
predicate in the common ambient kernel is fixed on the current source tuple;
it is not a test on a solved approximation of a child relation.

### 2.5 Which checked endpoint is covered

Fix an existing Pure source callable `f` with Value entry. Generate its
body/result presentation independently, giving the original `b,c`. At a
known instantiated callback slot `beta`, form the linked checked template
from that same synthesized presentation, its source carrier port `d`, the
actual entry, and the selected occurrence maps. Join the argument, rebind,
body, and consumer relations **before** projecting the output `[b,d]`.

The checked template keeps the actual callable descriptor and introduction
role. The slot supplies a typed invocation view. It neither resynthesizes
the body from expected endpoints nor creates a Handler wrapper around the
Pure value. Ordinary callback-literal generation B remains unchanged.

The theorem's query is this source-generated shared-body lift. The familiar
display `Fun(a,never,b,c) <: Fun(a,d,[b,d],c)` is only a mnemonic for that
role-indexed query. The proof gives no independent row interpretation to
`never`, and printed ports alone do not certify the hypothesis. An unrelated
callback annotation needs its own complete-contract adequacy theorem.

### 2.6 Exact lift pass and a local monotonicity lemma

The extra restriction in this section is material. Merely keeping segment
nodes, names, or incidence edges does **not** prove the theorem. The
concurrent [segment-bound objection](../progress/2026-10-04-direct-main-gate-attacks.md)
at `95ced93a` correctly rejects that weaker AST condition.

Here is the precise lift pass used in §2.5. It copies each generated source
relation constructor, with its entire old operand tuple and binder scopes.
At a copied source instruction it may add fresh **logical output coordinates**
defined by constructor expressions on that tuple: its source-region tag,
the already present invocation/view and typed-path references, or their
designated observation projection. These are graphs of total functions on
that instruction's well-formed tuples. At return, force, request, and
resumption nodes, they copy the corresponding source fields; at sequencing,
they join the child projections with the same pending-suffix references.
For a request-free prefix the corresponding event list is empty. At a latent
return the source-label/root references remain latent, not immediate events.

The occurrence *identities* are the original `d-`, `d+`, and `b+` slot
identities; the new coordinates name their derived projections and do not
freshen those identities. The selected complete typed views and static path
maps must already be present in the source instruction schema. A purported
projection needing an absent path, revived owner, new capture grant, or a
partial operation without its source witness is rejected by this generator
condition. Row flattening only displays the derived linked projection.

Freshness is logical freshness: these are not replacements for externally
fixed coordinates such as `nu(b)` or `nu(d)`. For Theorem C the old relation
already includes the source challenge's `d` constraints and the synthesized
body/result `b,c` constraints. Any test against those fixed coordinates must
be one of these existing local source clauses, not a new test introduced by
the lift. Only fresh derived-coordinate equations may be added. If an
alleged annotation map instead requires an unproved equality to a fixed
endpoint, this constructor test fails.

Most importantly, this lift pass adds **no independent predicate** restricting
an old segment witness through a newly chosen target bound. The argument's
`d` requirements were checked on the source challenge; the `b,c` presentation
is the same independently synthesized one. An annotated target that adds a
different condition is not an output of this pass, even if its printed row
is `[b,d]`. Witnessed reverse addition, when present, retains its original
attachment/subtraction evidence; no total subtraction operation is invoked.

**Local lemma.** All the admitted relational constructors are monotone in
their child relations. Moreover, the specified lift is a conservative
extension of each finite generated observation derivation: every old witness
has an extended witness, with the same old coordinates and observable source
behavior.

**Proof.** For monotonicity, an old conjunction/composition witness remains
a witness after either positive operand is enlarged; a union retains its
chosen branch; existential hiding retains the same witness; renaming changes
all incident coordinates consistently. Fixed source predicates are evaluated
on the same tuple. The two sequencing equations retain the first child's
tuple and the identical suffix, so the same argument applies after a request.
Fixed-position universal rigid binders are monotone pointwise as well; their
order is not exchanged with existentials.

For conservative extension, at a leaf evaluate the newly added constructor
expressions on the old tuple. Their totality gives a witness to every new
defining equation. None imposes a new condition on an old coordinate. At a
parent combine the child extensions using the same old shared coordinates;
the parent defines its new coordinates from that combined tuple, rather
than allowing independently chosen child copies of a shared witness.
Let `forget` delete only the added logical coordinates, and let `Obs` be the
common complete source-observation projection: results, requests, latent
source descriptors, history, and original identities/dependencies. Neither
map deletes a source event or an original receipt/profile identity. The
construction gives

```text
forget(w_plus) = w
Obs(w_plus) = Obs(w).
```

The displayed output row is an additional derived projection; it does not
replace this common observation. The induction above proves these equalities
for every finite generated derivation. The designated least relation has
exactly such finite derivation witnesses, including finite prefixes. A
recursive source label unfolds at each finite interaction depth, and all
finite future-use/resumption developments are covered by the same induction.
No separate fixed-point interpretation of `nu` is assumed. QED.

This lemma supplies the segment-bound transport law, including conservative
extras. It does not derive that law from a segment's execution soundness or
from graph-node identity alone, and does not posit preservation by an
otherwise unspecified `[b,d]` replacement.

## 3. Callback challenge admission without the tested query

A checked challenge certificate contains a finite source derivation with a
callable hole `H`, the known slot `beta`, an independently derived whole
argument carrier, typed response/future-use providers, immutable lexical
realization, the compatible decorated owner/view context, and one `nu,K,D`.
It also describes a finite legal interaction history.

The punctured derivation may use the hole's declared interface to describe
the context's uses of `H`. It contains **no** derivation that the Pure value
subsequently inserted in the hole already satisfies that interface. None of
its checks may cite the pending query `Q` or a consequence obtained by
assuming `Q`. Source nodes outside the hole are checked by their own local
rules, source declarations, typed paths, and constraints.

Define `D_checked` by these certificates, including the carrier's `d`
profile and its result interface `Value(a)`. Define `D_actual` by the same
source-context framework but the inlet generated by the actual Value-entry
derivation: receive the complete carrier, execute its designated port, and
use its typed `Value(a)` result path. The actual inlet has no incoming
support-row test inferred from Pure introduction or printed `never`.

Future-input admission is checked locally at the corresponding retained
source descriptor and current decorated context. Admission is not a claim
that a whole program already terminates or that its eventual outputs satisfy
the pending callback query. Returned-descriptor and response witnesses stay
in the joint history; this avoids admitting a response after a history that
did not produce its request.

More explicitly, the certificate relation is generated by the following
source rules:

- **Initial:** a locally typed whole-carrier derivation supplies its declared
  result port, profile, and path; the empty interaction prefix is admitted.
- **Response:** extend a prefix only at an exposed request tuple produced by
  the generated relation. Check the source provider at the original operation
  instance's declared response port, under that request's rigid witness and
  the retained continuation's current decorated context. No whole-Function
  comparison is a premise.
- **Resume again:** a retained raw handle must refer to a request already in
  the joint history. Reentry uses the same request witness and continuation;
  it is not admission of a fresh request.
- **Future call / force:** use only a returned source descriptor, its retained
  label and roots, and its original typed port. Check the next independent
  source provider, or the designated force-position certificate, in the
  current owner/view context. An expired initial callback slot is not revived.

The punctured context supplies these local provider rules before the hole is
filled. Histories instantiate them as request and returned-descriptor tuples
are produced; they do not require a derivation that the filling already
satisfies the hole's output contract. Thus dependence on a produced request
preserves the joint history without making admission depend on query `Q`.

This domain includes independently typed contexts that invoke an unused
export, as well as pure divergent carriers. It does not quantify merely over
already reached calls. It excludes corrupted states and unrepresented opaque
providers by the explicit source-certificate condition.

**A nonempty domain instance independent of Q.** Take `a=c=Unit`, empty
argument/body effect contributions, and a source context that invokes its
declared hole on `result(Unit)`. The Unit declaration, result constructor,
source application, known slot/view, and an empty immutable environment give
the punctured certificate without checking the hole's future filling. The
actual filling can be the separately generated Pure identity. Every inlet
premise is already in that certificate; Q is never a premise. This provides
an explicit nonempty instance. A particular unrelated unsatisfiable contract
may of course have an empty challenge domain; the definition does not assert
inhabitants for every type.

## 4. Theorem C: source-generated Pure-value callback lift

**Theorem C.** For the generator and source envelope of §§2–3, fix the
identity argument/result transport of the selected linked query, one joint
fiber `nu,K,D`, and its existing Pure callable with Value entry. Assume all
local source/primitive constraints other than the tested query hold at that
fiber. Then

```text
D_checked(nu,K,D) subset D_actual(nu,K,D)
for every h in D_checked:
    P_actual(h;nu,K,D) subset P_checked(h;nu,K,D).
```

The second inclusion concerns the entire generated bound, including
conservative local alternatives, latent interfaces, and every finite legal
future-use/resumption history. Its selected linked output projection is
admitted at `[b,d]` with the original occurrence/incidence evidence. Thus
typed-core §9's joint containment law proves the semantic linked lift.

### Proof

**Finite generation.** Preallocate each source label and binder, then emit
the bounded constructor template of §2.3 and references to its children.
Back edges reference existing labels. Size is linear in the finite decorated
source graph plus primitive, profile, path, and incidence descriptions.
This proves a finite relational description, not a finite-state execution
space, decidable higher-order inclusion, or principal inference.
The description is a recursive relational program. Identifying it with the
production finite endpoint representation, or effectively projecting its
denotation into that representation, remains a separate obligation.

**Source realization.** Induct on the challenge's source derivation. A
literal produces its typed descriptor. Lookup and aliases preserve one
lexical root. A closure/delay records the source label and captured roots;
binding extends that map by its result descriptor. Recursive references use
registered labels. No case requires a mutable-store replacement relation or
an opaque import. Plugging `f` for `H` preserves the surrounding graph and
slot identities before any claim of callback compatibility is made.

**Domain inclusion.** Let `h` have a checked certificate. It supplies the
whole carrier's designated computation, its complete latent structure,
typed result `Value(a)`, and rebind path. These are exactly the premises of
the actual Value inlet. Its additional `d` constraints do not invalidate
those premises when forgotten. Source owners, ambient configuration, and
response-provider roots are unchanged. Induction over the certified finite
input/future-use history repeats this argument at each inlet. Therefore
`h` is actual-admissible. Divergent carriers are included because admission
uses their source derivation, not an observed return or request.

**Inversion of the whole bound.** Take any `O in P_actual(h)`. Definition
§2.4 supplies one joint witness and a generated observation derivation.
Invert the constructor that supplied each step. A return uses its local
data relation; elimination uses the designated child; a call uses its
callee/argument/entry/body/consumer links; bind either enters its suffix with
the first child's result or retains that suffix after the child's request.
Repeated inversion gives constituent source-node witnesses for `O` at the
same external fiber. In particular a locally abstract alternative, even one
absent from exact concrete execution, has a local relation witness and the
same surrounding control derivation. This establishes the missing
factorization by induction on bound derivations; it was not assumed from
execution coverage.

**Reuse in the checked graph.** Copy those local witnesses and lexical roots
along the checked generator's source-node correspondence, using the
conservative-extension lemma in §2.6, not merely matching node names. Both
graphs use the same actual entry, independently synthesized body/result, primitive
relations, operation instances, and joint dependencies. Argument-origin
activity follows the generated `d-` Force path and its distinct `d+` linked
occurrence at the complete call. Body/consumer activity follows `b+`.
Each event joins these static maps with its actual `Observe`, `Path`, and
live-owner premises. Equality of row coordinates is not used to invent
that evidence. No request, receipt, grant, or maker activation is introduced.
Every constructor in the actual bound derivation consequently has a checked
constructor with the same witness, so its complete projection admits `O`.

**Latent values and resumption.** A request retains its original pending
suffix. After any certified response, apply the same constructor argument to
that suffix at the current decorated configuration. Repeated resumption
does not rebind a rigid operation witness or replay receipt. The supplied
owner kernel handles re-entry without restoring an expired shallow/maker
handler. A returned closure/delay retains its source label and captured
roots; the next certified use reveals the next source constructor.
Induction on finite interaction length, together with the same source-label
relation for recursive references, proves the clause for all finite future
uses. All finite prefixes of divergence correspond; no termination result
is inferred from empty support.

**Projection.** Hide only the permitted local witnesses once, after joining
the full relation. The selected `d+` and `b+` occurrences are its linked
output coordinates, so canonical flattening displays `[b,d]` without
independently solving the two marginals. This proves both inclusions and
the stated projection. The comparison law is applied to this one query;
successful concrete queries are never transitively composed. QED.

### 4.1 Nontrivial instance and failure controls

In proof notation take `f = lambda g. g(Unit)`, introduced as Pure. A
source-derived argument requests `E_arg`, then returns a captured closure
`g`; the body invokes it, it requests `E_body`, and it returns a closure or
delay. The complete invocation contains entry force, argument request,
typed rebind, a higher-order body invocation, another request, and a latent
return. The first contribution uses `d`; the second uses `b`; later uses of
the latent value retain their source-label interface. This is a derivation
example, not an assertion that a particular raw syntax has run in a compiler.

The old `{0}`/`{0,1}` countermodel fails the generator discipline if `1` was
added only at the actual root. If a local primitive legitimately admits `1`,
the checked construction reuses that primitive witness and its result
constraints. Exact execution support is unnecessary. Separately hiding a
shared witness also fails the explicit graph discipline.

Retained Computation entry is outside this Value-entry theorem. State,
arbitrary adapters, and opaque providers are outside its source grammar.
Internal handler images are excluded because a pre-dispatch observed event
can disappear from outward support: extending this proof must preserve the
handler relation before support projection. Ambient handler behavior is
copied on both sides, not replaced by a per-event outward-row test.

## 5. Structural: a finite source-generated ledger

The structural theorem uses the pure grammar and finite constructor signature in
[scoped projection §§2 and 6](2026-10-03-scoped-structural-projection.md): identity
atoms, Function, finite mandatory unique-label Records, and fixed-arity
constructors with declared variance. Equality is regular-tree equality;
`<:` is its coinductive structural relation. No global Top/Bottom or
optional Record relation is inserted.

For an explicit source-generation instance, take the monomorphic **pure
structural shadow** of finite source derivations. The following table
specifies its generator, rather than presuming a missing implementation.
Give each expression/binder a symbolic endpoint; allocate recursive binders
first. Constructor schemas in annotations are finite guarded graphs.

| Source derivation | Generated structural clauses |
|---|---|
| literal `e` | `T_e = declared_atom` |
| name `x` | `T_e = T_x` |
| lambda `x.body` | `T_e = Function(T_x,T_body)` |
| mandatory record | `T_e = Record{l:T_field_l}` |
| application `f a` | `T_f <: Function(T_a,T_e)` |
| known mandatory field selection `r.l` | `T_r <: Record{l:T_e}` |
| immutable binding | `T_x = T_rhs`, result endpoint from body |
| monomorphic recursive definitions | the same binder endpoints at every recursive reference |
| admitted structural annotation | its finite schema and the original directed checking clause |

This is a theorem-scoped structural constraint generator. It does not select
new evaluation/forcing rules, claim to model effects, or certify raw source
acceptance. In an effectful derivation these can only be its independently
justified structural obligations; arbitrary `Phi/K,D` is not discarded.

**Finite-generation lemma.** A finite derivation with finite annotation
schemas generates finitely many endpoints, descriptors, and clauses. Each
constructor emits bounded local data plus its source fields; references to
recursive binders do not recursively instantiate a new type schema.
Induction over the source graph after preallocation proves this claim.
Polymorphic recursion with unbounded new instances is not covered. Thus the
conditions below can be checked on source-generated data without unfolding
infinite types, guessing a model, or testing program termination.

Apply the existing successful
[rational equality quotient](2026-10-03-scoped-constraint-solving.md) and
[descriptor-known normalization](2026-10-03-open-residual-factorization.md).
Let `Q` be the finite quotient, `F` its descriptor-free classes, and `R` the
retained terminal inequalities, with all original bound identities retained.
The normalizer stops when either endpoint is free and otherwise descends
through known heads, width, and variance. It checks only finitely many
original-bound/node pairs. Its equivalence applies to arbitrary tree
assignments as well: local constructor equivalence and a post-fixed
simulation at recurring pairs do not require regularity of substituted holes.

The following proof never uses transitivity of the full Yulang concrete
compatibility relation. Its local steps are the normalized direct structural
rules and reflexivity of identical structural unfoldings.

## 6. Structural source predicates

Build the undirected graph on `F` whose edges are retained inequalities
between two free classes. Ignore orientation **only for this auxiliary
incidence graph**. Keep every oriented inequality in `R`. Its connected
components are called free components below.

For a free component `C`, let `Anch(C)` be the set of distinct nonfree
descriptor roots incident to it in retained free/descriptor inequalities,
in either direction. A descriptor is **closed** if it cannot reach a free
class in `Q`. These notions require only finite reachability and incidence.

Require the following source-ledger condition:

```text
For every free component C, either
  (G) every descriptor in Anch(C) is closed; or
  (A) Anch(C) consists of exactly one descriptor root.
```

Use case A only when that sole anchor is open; a no-anchor or all-closed
component belongs to G. Several original clauses may name the same anchor.
An A component can contain arbitrarily many free/free inequalities, cycles,
and aliases. Its anchor may reach that component, any other A component, or
G components through arbitrary constructor/variance paths.

For the main completeness theorem, use the following simple source-scope
condition: every input rigid identity is permitted at every free class.
The ordinary monomorphic case with no rigid identities satisfies it. This
is a finite test on lexical permission sets, not a permission bypass.
Primitive atoms are not rigid-name restrictions. The optional extension in
§8.2 allows narrower caps for a sufficient witness, with its stated limit.

This theorem excludes arbitrary generation guards, `Phi/K,D`, effects,
optional fields, and representation-identity predicates from the structural
decision problem. In an application, guards must be independently admitted
and additional relations stay conjoined. Failure of the incidence or scope
predicate means **outside this theorem**, never "ill typed."

## 7. Theorem S: regular completion with grounded checks and one open anchor

**Theorem S.** For a successfully normalized finite pure structural package
satisfying §6, arbitrary-tree satisfiability is equivalent to regular-tree
satisfiability. There is a terminating existence procedure and construction
of one simultaneous regular assignment. Original equations, directed bounds,
sharing, and the stated permissions are preserved.

### Construction

1. Retain all variables in G components individually, all their original
   free/free inequalities, and all their incident closed anchors and bounds.
   Decide this joint root-only package by the finite synchronous construction
   in [the root-only theorem](../progress/2026-10-04-root-only-regular-witness.md).
   Reject if it is unsatisfiable. Otherwise obtain one regular assignment.
2. For witness construction only, identify all free members of each A
   component and point that component to its sole descriptor anchor. Preserve
   all descriptor heads, exact masks, and child edges from `Q`.
3. Attach the regular graphs from step 1 at the G free roots. Interpret the
   resulting finite guarded graph by its regular unfoldings.

### Proof

**Necessity of the root-only checks.** Any model of the original package
satisfies every retained bound by normalization. Restrict its assignment to
G free roots. Every descriptor incident to G is closed already in `Q`, hence
its meaning does not depend on an A component. The restriction satisfies
exactly the root-only package of step 1. Consequently a root-only failure
refutes every full structural assignment within the theorem's hypotheses.

**Existence of a regular root-only assignment.** The root-only theorem is
complete even for an arbitrary-tree input model. It erases unmentioned
Record fields for existence and normalizes non-input atom names. Its finite
states jointly record free-track presence, closed-anchor nodes, and each
original bound's active orientation. A simultaneous head choice checks
matching heads and Record width; Function arguments reverse the same bound
token and results preserve it. All selected children are generated, including
those not currently inspected by a bound. Greatest-fixed-point deletion on
this finite state set terminates. A surviving state policy gives a regular
assignment, and its per-bound active tokens give direct post-fixed
simulations. No equality of original subtrees is inferred from equal state
profiles. For other constructors in the fixed finite signature, add the tagged
coordinates `Child(C,i)` for every declared head and child position, disjoint
from Function `Arg/Result` and Record `Field(l)` coordinates. The same finite
transition adds their declared same/reversed/both child obligations. Thus both
the head alphabet and the complete tagged child alphabet remain finite.

Use only input rigid names or primitive/default Record choices in this
existence construction. Under the scope condition in §6 every such rigid is
permitted at every G root. No unseen rigid needs to be introduced.
For precision, a non-input atom can be uniformly replaced by the empty
Record when no safe primitive representative is chosen. Compared atoms were
equal, and no fixed closed anchor contains a non-input atom, so each affected
comparison becomes `{} <: {}`. This preserves existence and introduces no
fresh rigid; it does not claim to preserve the entire solution fiber.

**Consistency of the A reconstruction.** The free/free component collapse
is a witness choice. Every collapsed component has exactly one descriptor
target; there is no competing descriptor to unify with it. Multiple
components can point to the same anchor. Following these alias pointers
stops at a prescribed descriptor. A descriptor-child edge is a constructor
edge, not an equality merging that descriptor with its child. Thus a cycle
through an anchor and one of its children is productive recursion, not a
head clash. Every cycle remaining after alias elimination is constructor
guarded, and there are finitely many nodes. The attached G graphs are closed
regular graphs. The whole graph therefore has a well-defined contractive
regular unfolding at every original root.

**Original clauses.** Original quotient equations hold because their heads
and child references were retained. In G, all bounds hold by step 1. Each
free/free edge of an A component now has equal endpoints. Each incident
free/descriptor edge also has equal endpoints because it uses that
component's sole anchor, regardless of its original orientation. Equality
of unfoldings witnesses reflexive structural comparison coinductively,
including Function reversal and every required Record/constructor child.
No free/free edge connects two distinct components by definition. These
cases exhaust `R`. Normalization equivalence then supplies each original
bound under its original identity. The scope condition admits every rigid
reachable in the reconstructed graph, proving permission preservation.

**Completeness and termination.** A full arbitrary model implies root-only
satisfiability by the first paragraph; the finite construction then gives a
full regular model. Conversely any constructed regular model is also an
arbitrary model. All normalization, reachability, component, and alias work
is finite; the only search is the finite root-only fixed point. This proves
the equivalence and termination. It is not a polynomial-time claim. QED.

### 7.1 Finite witness size

If `N` is the quotient size and `M` the total nodes of the selected joint
root-only witness, reconstruction needs at most `N+M` nodes before harmless
sharing/default-node optimizations. It does not unfold descriptor prefixes
or fold independently chosen activation occurrences. If there are no G
constraints, unanchored G roots can all use the empty Record.

This bound concerns **one existence witness**. It gives no uniform bound on
the size of every solution and no equality-preserving quotient of the full
solution fiber.

## 8. Structural examples and necessary limits

### 8.1 Actual open recursive Function feedback

The structural shadow of `lambda x. x x` contains

```text
D = Function(X,R)
X <: D.
```

Its single open anchor is `D`; choose `R={}`. The construction gives
`X = Function(X,{})`. This retains the prefix-shifted descriptor equation
and a Function comparison that reverses argument direction. It is not a
closed-type check or a root-only case with all open descriptors removed.
This is a proof-core derivation, not an executed Yulang fixture.

More generally,

```text
P = Function(Y,{left:X})
R = {next:X,payload:Int}
X <: P
Y <: R
```

produces the finite mutually recursive witness `X=P`, `Y=R`. Free/free
constraints may add any number of variables to either component if its
distinct open anchor stays unique. Bound orientation may be reversed.

The source can also compare recursive schemas with open payloads:

```text
P = Function(a,{next:P,value:b})
Q = Function(c,{next:Q,value:d,tag:Int})
Q <: P.
```

Known-head normalization follows the recursive schemas and leaves
`a <: c`, `d <: b`. These are G constraints; mandatory width admits `tag`.
Several incompatible closed requirements on a G group can still make the
procedure reject. The theorem is therefore not just an always-satisfiable
single-equation fragment.

### 8.2 Narrower permissions: sufficient witness, not a completeness claim

For a package with only A components and unconstrained default components,
or after selecting a G witness, arbitrary finite caps can be checked by
propagating them through the resulting finite graph. If every reachable
rigid is permitted at every restricted root, the constructed witness also
satisfies those original caps. This is a terminating sufficient extension.
If this check fails, the package is outside that sufficient result; another
structural assignment may still satisfy it.

For example, let `kappa` be forbidden in `X`:

```text
D = Function({f:kappa},X)
X <: D.
```

Equality reconstruction would put `kappa` inside `X`, but the original
bound has the permitted regular witness `X=Function({},X)`. Function
contravariance asks for `{f:kappa} <: {}`, which holds by width. Thus a
failed candidate cap check cannot be treated as original unsatisfiability.

### 8.3 One witness is not the principal solution relation

For `X <: {}`, the construction can choose `X={}`. The original relation
also permits Records with additional fields and arbitrarily complex
payloads. No equality is inserted into the retained inference ledger.
Witness-only component collapse similarly does not identify independent
source ports in the principal presentation.

Keep the existing finite residual expression and all original endpoints,
constraints, `Guard`, and `Phi/K,D` intact. Theorem S certifies existence in
its pure structural subproblem. It does not prove effective principal
projection, arbitrary joint predicate solving, or the SCC lifecycle theorem.

### 8.4 Why the failed meet fold is irrelevant to this construction

For the recorded example `Y=Function(Y,{f:Int})`, `X <: Y`, Theorem S
chooses `X=Y`. It does not meet the subtrees of an arbitrary alternative
solution or identify address occurrences by their observed head profiles.
Each reconstructed bound has an actual direct structural simulation.
The prior child-coherence/activation counterexample is preserved as a
counterexample to that fold and is not asserted to refute regular completion.

## 9. What the source hypotheses add, and what remains open

Theorem C replaces the unproved general bound inversion with an explicit
constructor discipline that proves inversion. Theorem S replaces an
unproved general finite-model property with a finite incidence predicate
that admits a direct model construction plus a root-only decision kernel.
Both conditions can be audited from a source derivation and generated graph,
without using the result of the tested query or searching for an unknown
regular invariant.

The restrictions are material. C requires the generated shared-body lift,
locally attached abstraction, represented providers, and the stated immutable
source core. S excludes a free component with two distinct anchors when one
is open, unless an independent stronger theorem applies. Source-generation
alone, without these conditions, has not been proved sufficient.

The concurrent [first-order compositional-premise result](../progress/2026-10-04-callback-compositional-premise.md)
isolates a compatible bounded recipe obligation and the same missing B step-6
emission rule. Theorem C explicitly constructs its generator and covers the
stated finite latent developments; neither result implies that the current
unrestricted B contract already entails that construction.
In particular, the operational graph supplied by typed-core §9 and a finite
inference endpoint are distinct. A finite source graph alone does not prove
the abstraction/representation bridge between them.

The unrestricted callback annotation/complete-endpoint theorem, unrestricted
structural finite-model conjecture, State/reference/import bridge, general
polymorphic instance generation, joint effects, principal projection, and
generalization/intrusion lifecycle remain open. No compiler implementation
gate is opened by these conditional theorems.

## 10. Review and verification

Independent callback and structural compiler referees reviewed their
respective proof scopes; a separate spec auditor reviewed the source and
authority boundaries. The initial callback and scope reviews found no
findings. The structural review found no blocking/major issue and requested
one minor clarification: explicitly use the finite constructor signature from scoped
projection §6 and its tagged child coordinates. That clarification is
incorporated above. A source-producer cross-check separately confirmed the
G/A composition, but is not counted as independent certification.

Concurrent upstream evidence then exposed a major gap in the weaker callback
AST-preservation condition. The primary accepted the callback referee's
focused reconsideration, specified the exact conservative-extension pass,
fixed the recursive interpretation, and made admission/freshness/observation
preservation explicit in §§2.4–2.6 and 3. A fresh independent callback referee
reviewed only this repair and its use in Theorem C, finding no blocking/major
issue and requiring no further material fix. The full generator/annotation
and raw-source correspondence remain outside that certification.

Fifteen focused mathematical checks evaluated explicit regular graph
witnesses, variance/width directions, cross-component reconstruction,
permission and principality counterexamples, local bound slack, and joint
witness correlation. These checks are examples, not an exhaustive theorem
test. The proofs were not checked by a proof assistant.

This is M3 mathematical work. Compiler tests and performance measurements
cannot certify these arguments and were not run for this documentation-only
change. Exact review scopes, limitations, and deterministic document checks
are recorded in the paired
[progress note](../progress/2026-10-04-source-generated-theorems.md).
