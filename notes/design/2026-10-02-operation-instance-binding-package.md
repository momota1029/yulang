# Operation instances, handler arms and shared resumption witnesses

Date: 2026-10-02
Status: Draft; source-proof package; no implementation authority
Scope: operation-local binder protocol, selected-instance compatibility, lifecycle dependency
Approved-by: none for a new inference/generalization rule
Drafted-by: primary with bounded architect and frozen-source audits
Reviewed-by: compiler_referee and spec_auditor; scoped M3 package review; independent compiler_referee generic-arm correction delta, no findings
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
