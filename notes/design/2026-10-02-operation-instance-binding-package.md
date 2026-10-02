# Operation instances, handler arms and shared resumption witnesses

Date: 2026-10-02
Status: Draft; source-proof package; no implementation authority
Scope: operation-local binder protocol, selected-instance compatibility, lifecycle dependency
Approved-by: none for a new inference/generalization rule
Drafted-by: primary with bounded architect and frozen-source audits
Reviewed-by: compiler_referee and spec_auditor; scoped M3 package review; independent compiler_referee generic-arm correction delta, no findings
Scoped-template-review: §§7–9 independently reviewed by compiler_referee and spec_auditor; no findings in the declared fragment
Supersedes: no source decision; refines the existing complete OpCompat obligation

## 1. Existing authority and the missing distinction

The coupled-interface core already requires compatibility for **every
reachable selected request**, not for an existentially chosen compatible
subset. This selected-request condition is necessary, not sufficient for
source declaration acceptance. Charter §19 records the user's correction:
operation-local declaration binders require uniform arm checking; observed
caller instances cannot specialize those binders to make an arm acceptable.

The frozen parameterless `assertion::assert_eq` declaration demonstrates
operation-local value and callback-effect variables not determined by the
family projection. The register-quotient package §7 records that evidence.
Consequently family equality cannot replace complete instance compatibility.

This package derives binder ownership and local transport from one complete
declaration view. It is a **new successor construction** for the selected
Yulang effect semantics, not a Simple-sub-original rule. Operation polymorphism
is an evidenced source capability; its complete inference and safe interaction
with generalization remain proof obligations. Nothing here changes primitive
shallow handling, inert whole-argument reification or source result forwarding.

## 2. Declaration instantiation and instance retention

Write the existing declaration as

```text
Delta |- op p : forall rho_family, beta_local. Sigma(rho,beta)
Sigma = (payload A, response B, complete typed interface/profile Lambda)
family projection = F(rho_family).
```

`Delta` contains rigid imports and already-shared endpoints. `beta_local`
contains declaration binders absent from the family parameter tuple;
occurrences of those binders in nested callback effects remain part of the
same signature. A binder is classified by ownership, not by whether its
current assigned type happens to equal a family argument.

One typed use/instantiation of a generalized operation declaration supplies
one capture-avoiding map `theta`, fixing `Delta`:

```text
OpInst(p,theta) = (p, F(theta(rho)), Atheta, Btheta, Lambdatheta).
```

The family-support projection is not injective: two maps can agree on
`rho` and differ on `beta`, hence give the same typed row point but different
payload or callback interfaces. Even adding the operation path does not
recover the omitted local coordinates. Retain them in the complete request
view and its existing `K,D`; do not add them to source family arguments by
fiat. The register-quotient theorem over family points therefore needs these
additional retained coordinates/parameters for an application to complete
compatibility. Its row colors alone cannot reconstruct them.

This states the correspondence required of instantiation, not the later
proof of the generalizer. A lookup of an already instantiated monomorphic
value, its aliases, carrier construction, dynamic request emission and raw
resumption do not independently instantiate this signature. Separately typed
uses of a generalized declaration may have distinct local maps even when
their family projections coincide. Static use-site freshening and fresh
dynamic request/event identities are different operations.

The typed request retains

```text
(OpInst(p,theta), payload : Atheta,
 raw continuation : Btheta => J_q, Ktheta, Dtheta).
```

`J_q` is the complete raw-suffix interface under the current resumed state.
It is not replaced with the handler arm's return interface. A shallow
resumption does not automatically reinstall the selected handler or acquire
the derived deep handler's result type. Lambda contains the signature's
typed paths; no outer callback effect is copied to unrelated descendants.

Opening a request view gives the arm names for this already chosen instance.
It does not choose new values for `beta_local`. One may model that opening
as an existential package elimination, but this is proof notation for the
retained view, not a new source type or runtime packaging requirement.
Every name introduced by the opening remains related to `theta` throughout
the payload, raw continuation, latent values and live dependency incidence.

## 3. Arm compatibility over the same instance

The arm's executable body, captured environment and source annotations are
fixed. To check the declaration, fix the admitted family instance and open
`beta_local` as fresh rigid names `kappa`. Check the arm uniformly under
those names and the declaration's bounds, keeping captured/shared endpoints
shared. Caller sites cannot solve `kappa = Int`. Only after this checking
proof is established may it be instantiated at the actual retained `theta`;
do not derive a second unrelated operation-local witness from family equality.

The independent arm-body typing demands remain. For each selected request:

1. its exact operation and invariant family instance agree with the selected
   arm's declared operation/family contract;
2. payload `Atheta` can be transported to the arm's actual input demand;
3. every response the arm supplies to this raw continuation is accepted at
   `Btheta`;
4. complete callback/effect/profile obligations are transported from
   `Lambdatheta` along the actual typed paths, retaining all dependent `K,D`;
5. the arm computation and raw suffix respect their own source interfaces,
   the captured environment and the current store invariant.

These are the existing `OpCompat` premises with binder ownership made
explicit. Using the same declaration view does not prove the arm-body
demands automatically, eliminate admitted value conversions, or decide
Function inclusion. The resulting relation can be written `Psi_h(theta,nu)`;
the notation is not an effective solver or a new obligation kind.

The existing preservation quantifier is

```text
for every nu,q,h:
    ReachSel_nu(q,h) implies Psi_h(theta_q,nu).
```

For several selected instances, all resulting conditions are joined under
the same `nu` for captured/shared endpoints. Independent operation-local
maps are not merged by family, and the captured environment is not freshly
solved once per event. A handler-body constraint cannot discard a reached
request from this implication. Runtime search still selects by the common
ordered visibility/pattern/guard relation before the compatibility obligation.
An incompatible selection is not forwarding.

A uniformly checked arm proof can be instantiated at every admissible
retained local substitution, establishing the selected-request implication.
The converse does not establish source declaration acceptance. The prior
Int-only example is rejected by the user: for generic `sink::put : 'a -> ()`,
an arm containing `my checked: int = x` is unacceptable even if all actual
selected calls supply Int. Its rigid local input cannot be solved from those
calls. Specializing a family parameter, using a concrete operation signature,
or using the declaration's explicit bounds is distinct from specializing
an unconstrained operation-local binder. Complete inference and completeness
for uniformly checked generic arms remain unproved here.

## 4. Local preservation and declaration transport

**Theorem scope.** Fix a well-formed store/environment and one selected
request instance satisfying the five arm premises above. All values are
used at their established interfaces; no dependent witness is independently
generalized in this theorem. Then payload delivery and any finite sequence
of typed uses/resumptions preserve the operation's instance correspondence,
the continuation response interface and symbolic family dependencies.

**Proof.** Payload transport gives the actual arm input its required type
and carries the packet's typed evidence by common `Flow`. The raw
continuation retains `Btheta` and `J_q`. At a resume, premise 3 supplies a
value admitted by that same `Btheta`; ordinary continuation application
therefore enters its saved suffix with the current state. No step chooses
another declaration substitution. Premises 4–5 and the reviewed shallow
source theorem carry latent paths, store references, request origins and
symbolic `K,D` through the suffix. Storing or returning a dependent value
retains the packet's witness through its corresponding path. Repeating
the argument covers multiple resumptions and later uses, provided each
new state and supplied response meet the same premises. Re-entry follows
the source suffix and does not restore the consumed handler.

This is a local preservation theorem with explicit typing/store premises,
not a proof that inference enforces them under arbitrary let-polymorphism.

There is also a finite constructive signature-transport result. Given a
finite declaration graph of representation size `s` (nodes, edges and
profile/incidence entries) with named binder leaves, allocate
one image node per node and rewrite each binder leaf through `theta`.
Preserve back edges, sharing and original profile/path occurrence IDs.
This produces `Atheta,Btheta,Lambdatheta` together in `O(s+|theta|)` graph
work, using references to substituted endpoint graphs rather than copying
or unfolding them. The bound assumes indexed binder substitution lookup;
it counts adjacency entries even when many point to the same shared node.
It introduces no force or type-shape adapter.
The graph induction gives, for any consistently capture-avoiding endpoint
substitution `sigma`,

```text
sigma(Sigma theta) = Sigma (sigma composed with theta)
```

with rigid imports treated consistently on both sides. The same map acts
on all predicate payloads and incidence references. Thus sharing does not
have to be reconstructed after materialization. This construction does
not solve resulting constraints or prove which binders may be generalized.

Fresh proof names are permitted when accompanied by their capture-avoiding
correspondence to the same instance. In particular, a static resumption
typing rule may use fresh rigid names to express a uniformity requirement.
That is different from runtime re-instantiation or independently assigning
different concrete types to the same captured witness on two resumptions.
The protocol forbids the latter; it does not ban the former by spelling.

## 5. Why local sharing is not the generalization theorem

Sekiyama and Igarashi's
[Handling polymorphic algebraic effects, §§2.3–2.4](https://arxiv.org/pdf/1811.07332)
exhibits unsound effectful-let generalization with interfering resumptions.
Its deep, call-by-value calculus and proposed checking restriction are not
successor authority.

Adapt the attack to the shallow core with
`fetch : forall a. Unit -> (a -> a)`. Assume, **only for the attack**,
unjustified generalization of its returned `f` in the suffix:

```text
C(f) = if f(true) then f(0) + 1 else 2
```

The arm invokes raw `k` with `v(x) = (k(const x); x)`. Then
`k(v)` enters `C(v)`, whose `v(true)` invokes `k(const true)`.
In the nested `C(const true)`, the Boolean test succeeds, but the integer
call also returns `true`: execution reaches `true + 1`. A captured value
has crossed incompatible instantiations through nested resumption.

There is no later operation in this suffix, so the trace does not depend on
reinstalling a handler. Receiver entry forces the Boolean/integer arguments
at their ordinary value-parameter demand; no argument construction prefix
or recursive latent-result force is needed. This is a source-core attack
on the hypothesized typing/generalization rule, **not** evidence that the
frozen compiler accepts it, nor a counterexample to selected preservation,
typed boundary transport or shallow handling.

At a single fixed instance, `f` cannot independently acquire Boolean and
integer instantiations. The attack's extra power came from the assumed
generalization, so the local theorem's premise does not hold there. Naming
one operation-local witness on the request is not by itself a proof that
future source bindings will retain this restriction.

The later lifecycle theorem must establish when operation-local witnesses
and dependent values can be abstracted without this interference. It may
not silently quantify a witness still incident to the payload, response,
continuation, store or result views. This statement sets a proof obligation,
not a new value restriction, linearity requirement, signature restriction,
or rejection of all effectful generalization. A proposed restriction needs
its own compatibility/proof treatment before implementation.

## 6. Frozen evidence and remaining milestone

Bounded `a58eefc3` audit, no tests executed:

| Evidence | Meaning and limit |
|---|---|
| `lib/std/testing.yu:10–17`, generic public-use fixture already in register-quotient §7 | independent operation-local value/effect parameters exist; no handler-generalization theorem |
| `crates/yulang/src/source/tests/case_01.rs:311–329` | `get:Unit -> t` under family `var t`, with an arm resuming at Int; family-parameter specialization, not an operation-local response witness |
| `crates/infer/src/lowering/tests/case_03.rs:962–972,1003–1012` | generic state handler threads a value through recursive resumptions; no polymorphic stored resumption |
| `crates/infer/src/lowering/control.rs:1114–1133,1235–1269,1328–1353` | one fresh named-signature map per syntactic arm connects family/payload/result; only family variables enter row arguments |
| same file, `1562–1586,1603–1628` | continuation input shares the operation-result variable; continuation is a lexical parameter, not independently generalized here |
| `crates/infer/src/lowering/name_ref.rs:94–112` and the lifecycle/selection path | ordinary static reference instantiation, not runtime per-event inference |

The audit did not locate a fixture for two local type instantiations of one
parameterless operation under one handler, an independent operation-local
result variable, or a polymorphically stored resumption. Those capabilities
are not certified or prohibited by the absence of fixtures. Frozen fresh
variables do not prove uniform generic-arm checking or safe specialization.
Charter §19's source correction governs operation-local arm checking; the
reachable-selection condition remains a necessary preservation obligation.

This package closes declaration-local ownership/transport and the local
payload-to-resume correspondence within its stated premises. It does not
compute full `Psi_h` or settle generic operation inference. The next source
checking construction must check body demands uniformly under rigid local
declaration binders, instantiate the checked proof at retained request views,
and retain constraints for every selected instance,
including operation-local callback effect parameters. Its interface must
expose live dependencies needed by the later generalization proof; a finite
register quotient cannot hide them or solve their scope by family equality.

Full finite/principal source presentation, safe generalization, fresh
instantiation, SCC intrusion, the later method/role gate and implementation
remain open. The source protocol and interference attack need no new user
semantic decision at this point. The prior review's local conditional safety
and request-instance transport scope remains; its source-acceptance claims
are corrected above. Independent delta review closes this correction, not
the remaining generic-arm inference/completeness proof.

## 7. One uniform checking template and its request instances

The source correction removes the need to infer a caller-restricted type
that legitimizes a non-generic operation arm. It does not remove the arm's
actual execution or the operation's dependent signature.

For an arm of `forall rho_family,beta_local. Sigma(rho,beta)`, fix the
handler's family instance and its captured environment. Allocate one rigid
checking name per local declaration binder, and one shared map from all
signature occurrences to those names. Bind the payload at `A(rho,kappa)`
and the raw continuation at `B(rho,kappa) => J_raw`. Generate the body and
its source consumers once under this environment. The complete raw suffix
is an interface parameter, not the arm's output or an implicitly deep result.

The scope of a candidate checking relation is

```text
exists Z_shared.
  forall kappa_local.
    DeclBounds(rho,kappa) implies
      exists Z_body. BodyConstraints(Gamma,rho,kappa,Z_shared,Z_body).
```

Shared/captured endpoints must have one interpretation outside the local
universal. Body-local witnesses may depend on the enclosing rigid names.
Nested generic declarations retain nested scopes; moving an already-shared
witness inward is not an optimization. All predicate and path references
remain part of the same `K,D` graph.

This formula states the scope contract, not an effective solver by itself.
In particular, truth obtained by separately elaborating a different arm at
each concrete `kappa` is insufficient. A checking proof must supply one
finite source body/consumer template and a substitution-stable derivation.
Source roles, introduction/elimination sites and actual boundary contracts
remain fixed. Unknown-shape adapters cannot be smuggled into a body witness
as a new program chosen separately for each request.

### Uniform-instantiation theorem

Assume such a checked generic template, with substitution-preserving rules
for its body primitives. Let `theta` be an actual retained operation map
at the fixed family instance, satisfying the declaration's bounds. Then
specializing the generic proof by `kappa := theta(beta_local)` supplies the
corresponding payload, body and response proof under the same captured
assignment. It does not independently infer the arm at that request.

The actual store and raw suffix must meet the template's existing typing
assumptions, including its `J_raw` parameter. `theta` substitutes declaration
binders; it does not itself establish a bound on the current suffix's effects.
That obligation remains in the complete invocation/handler image.

**Proof.** Alpha-rename bound proof names to avoid the actual endpoints.
Instantiate universal elimination at the complete local tuple of `theta`;
the actual declaration bounds discharge its antecedent. Shared witnesses
are unchanged, while the body witnesses follow the checked proof's scope.
For each source rule, use the same rule and transport its operand tuple.
Core §6's result/consumer substitution law preserves source roles and force
positions; operation §4's signature law preserves payload/response sharing;
common typed `Flow` transports original profiles and `D` with their `K`
references. Any primitive not yet proved substitution-preserving remains a
premise of this theorem, not an opaque solved inclusion check.

Every use of the raw continuation therefore supplies a value admitted by
that same `Btheta` and enters the same `J_raw` under the current state.
The existing shallow local-preservation theorem applies, including repeated
resumption and later latent uses under its store/typing premises. Nothing
reinstalls the consumed handler. Fresh proof names denote the retained
instance; they are not fresh runtime or independently solved type instances.
Different requests may specialize the template differently, but they never
re-solve the captured environment separately.

Consequently declaration validity can be established without enumerating
future callers' operation-local maps. Actual requests still need their maps
for execution, return/resumption correspondence and effect constraints.
Generic validity alone does not calculate a handler's outward image.

## 8. Constructive equality kernel for scoped templates

There is a small effective fragment within the checking template. It is
useful for constructor/invariant endpoint equalities; it is not a replacement
for source subtype checking.

### Input and solution language

Take a finite conjunction of equations over finite, acyclic free-constructor
terms. Constructors have fixed arity and no equations such as commutativity,
idempotence or recursive unfolding. There are rigid checking symbols
`kappa` and existential inference variables `X`. Each `X` has a finite set
`Allowed(X)` of enclosing rigid names on which its solution may depend.
Earlier captured variables have no permission to mention a later arm binder.

A solution is a **uniform syntactic constructor substitution**, preserving
rigid symbols and respecting these dependency sets. Residual existential
variables carry dependency sets too. Substitutions are ordered by further
scope-respecting instantiation. This is the expressible equality fragment
for which principality is claimed; it is not arbitrary pointwise choice of
semantic witnesses or a theorem about all quantified first-order formulas.
Its ground interpretation is a nontrivial free term algebra. Rigid symbols
denote universally substitutable parameters, not concrete disjoint type tags.

Excluded here: subtype inequalities, declared bounds/implications, disjunction,
semantic row equality, recursive/equi-recursive types, higher-order interface
inclusion, and source generalization. The whole source constraints keep those
obligations; this kernel cannot declare them discharged.

### Finite procedure

Maintain a term DAG, substitutions, an equation worklist and dependency sets.
Dereference existing bindings before each step.

1. Delete identical equations. Decompose equal constructor heads into the
   corresponding child equations.
2. Distinct constructor heads, distinct rigid symbols, or a rigid symbol
   versus a constructor are a failed **uniform equality obligation**.
3. Orient an equation with existential `X` on the left. Reject a genuine
   occurs-cycle. For `X = t`, every rigid symbol occurring in `t` must belong
   to `Allowed(X)`.
4. For every remaining free existential `Y` in `t`, intersect `Allowed(Y)`
   with `Allowed(X)`. Propagate such restrictions through existing bindings
   and reject any newly forbidden rigid occurrence. Then bind `X` to `t`.
   For variable aliases, their permitted dependency set is the intersection.

Removing the permission to mention a rigid name constrains a still-unsolved
variable; it does not immediately reject that variable. It may still be
solved by a term using only the common permitted names, or by a ground term.

Use visited constructor pairs and a worklist for scope decreases. No new
term constructors are generated. Each variable is bound at most once after
dereferencing; each finite dependency set can strictly decrease only finitely
often; the finite DAG has finitely many constructor pairs. Thus the procedure
terminates. No useful runtime bound or compiler resource threshold is claimed.

### Preservation and relative principality

Constructor decomposition and deletion preserve the solution set. A free
constructor substitution cannot repair a rigid/head clash or a finite-term
occurs-cycle. For `X=t`, any solution must assign the same term to both sides.
Every rigid occurrence explicitly in `t` must therefore be allowed at `X`.
Every free variable occurring in that term must likewise lose dependencies
forbidden at `X`: free constructor contexts cannot cancel an occurrence.
The intersection step records exactly this restriction, without choosing
the remaining variable's value.

Conversely, a solution of the residual equations and restricted scopes
extends through `X=t` to a solution before the step. Induction on the finite
run gives both failure correctness and factorization: every admitted uniform
solution factors through the returned substitution via an instantiation of
its residual variables that respects their retained scopes. The returned
substitution is therefore principal in this fragment's stated order.

Evaluating a solved syntactic equality at any assignment of its rigid names
preserves equality, so the result is sound for every such instance. A failed
uniform equality does **not** assert that its two sides are disjoint at each
instance. For example, the obligation `kappa = Int` fails uniformly, but
`kappa := Int` is a valid actual request instance. In particular, no rule
`kappa intersection Int = Bottom` follows from rigidity.

Examples of the scope mechanism:

```text
forall kappa. exists X. X = Box(kappa)       succeeds: X := Box(kappa)
exists X. forall kappa. X = Box(kappa)       fails: kappa outside Allowed(X)
X_outer = Y_inner                           retains a shared residual variable
                                            with intersected dependencies
```

These are equality-kernel examples, not a decision to replace subtyping by
equality. The user's `checked:int=x` example is rejected by the generic
source rule. Its ordinary assignment obligation need not literally be an
equality node; any admitted checking rule must establish it uniformly under
the rigid input, and actual Int callers cannot supply that proof.

## 9. Source consequences and remaining execution image

For the schematic generic operation `echo : 'a -> 'a`, an arm's payload
and raw continuation response share the same rigid name. Passing that
payload back with `k x` preserves the correspondence. Unconditionally
resuming with Int cannot be justified for an unconstrained arbitrary local
response type. A response fixed by a family parameter already instantiated
at Int is a different case. These are source-rule illustrations, not executed
Oracle fixtures or complete handler acceptance tests.

The scoped equality kernel gives an effective piece of template checking,
and the uniform-instantiation theorem removes caller enumeration from generic
arm validity. Neither establishes full subtype/scoped constraint solving or
the **complete invocation and shallow-handler image**. A generic arm may
execute a callback with a symbolic effect, expose other operations, or resume
a suffix that exposes the same family after the selected handler is gone.
It may therefore be valid while its result still has residual effects.

The next common execution template must derive entry, callback, selected-arm
and raw-suffix effects under actual ordered visibility. It cannot subtract a
whole family merely because every arm is generic, nor erase operation-local
maps whose endpoints remain incident to those effects or results. Source
template generation, principal solving for the complete interface and the
later lifecycle/implementation gates remain open.
