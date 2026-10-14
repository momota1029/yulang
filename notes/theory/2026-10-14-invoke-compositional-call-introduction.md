# `invoke`: compositional complete-Call introduction

Date: 2026-10-14
Status: Draft mathematical constructor completion; conditional derivation independently reviewed after repair; no production or parent certification
Baseline: `add2fdf4c12e7379e1c5ad2c24b5023320262ae3`
Branch: `research/simple-sub-intrusion`
Definition authorization: the user's current instruction, "定義が必要なら定義すればいい"
Scope: the new source case is strictly
`Apply(Name(resolved unannotated Value formal), Integer literal)`, specialized
below to the body of `my invoke f = f 1`, from its source children and
independently declared local primitives. This is a definition/proof domain,
not a compiler support restriction. No new inference search, public type
constructor, or production cutover.

## 1. The change in method

Do not take `OriginalGenCall0(c)`, `TypedCallCert(c)`, `C0(c)`, or a complete
already-typed Call kernel as an input. Define the missing compositional
introduction and prove its typing by cases on its constructors.

The primitive signature remains the one in Source Generalize L1: local
primitive meanings, typed operand/result interfaces, licenses, guards and
world/provider/future laws, fixed independently of this source Application.
That signature is not a certificate about `f 1`. In particular a primitive
called `CallIsTyped(c)` is not an admissible way to discharge this construction.

The important design choice is **branch-preserving result synthesis**. The
result contract is assembled from the receiver's complete result contract and
each independently declared alternative's own complete result contract. It is
not the receiver's contract imposed as a filter on all other alternatives.
This choice avoids both a missing whole-Call typing premise and silent deletion
of alternatives. The exact whole membership relation is retained alongside
this result contract, so taking a result union does not uncorrelate the Call.

This completes one new source-constructor case. It leaves old source-rule
cases available. It does not identify the new case with a separately fixed
opaque historical relation whose constructors have not been provided. The
source/native representation theorem and public principal projection are not
claimed here.

## 2. Existing constructors used, without replacing their meanings

The governing interfaces are:

- [Source Generalize](2026-10-08-source-generalize-definition-and-proof.md),
  L1-L5 and sections 3.1-3.3: primitive, Name, Literal, Parameter, Lambda,
  Result, Delay, Bind, checking, and their original ordered telescopes.
- [The source-owned Lambda](2026-10-11-invoke-original-call-proof.md), 4.1:
  `F_L = Strict(I_f, formal:A_f, R_L, IF_L)` and the same-frame entry map.
- [Contextual Function membership](../design/2026-10-08-contextual-function-membership-definition.md),
  2-3: independently formed challenges; acceptance and complete observations
  at each genuine actual provider; hereditary immutable membership.
- [Complete Call](../design/2026-10-07-complete-call-contribution-definition.md),
  2-4, and [source interfaces](../design/2026-10-08-call-source-interface-definition.md),
  2-3: callee Bind, actual receiver execution, all original alternative clauses,
  IF-Insert/IF-Use, open carriers, and output-dependent future interfaces.
- [Constrained presentations](../design/2026-10-05-source-contracts-and-common-allowance.md),
  2.1-2.2 and 3.7: joint conjunction/union, scoped binding, constructor images,
  independent descriptor membership, and evidence-preserving abstract arms.
- [Application_N](2026-10-08-flat-application-owner-completion-decision-object.md),
  4-6: useful static source spine, not a proof of complete Call typing.

Only Call composition and its source-owned formation are completed here.
`Return`, `Delay`, primitive validity and complete Function membership are not
redefined as membership in this newly generated source program.

## 3. Types of the local inputs

### 3.1 One dependent frame

Fix the actual source nodes `L,d_f,u_f,c,a` and `Resolve(u_f,d_f)`. All objects
below are indexed by their original binder tree and one joint `xi=(nu,K,D)`.
Write `h : H_c` for a full independently valid input frame of the Call. Its
fields include the original environment, event/world, callee hole and the
**open** whole-carrier hole with its declared contract. They are not independent
per-port existential choices.

Write `o : Obs_c(h)` for the full original observation tuple. It includes the
Return or pending prefix, current guards, actual providers/worlds, receipt,
response, raw resumption, ordered continuation and compatible future-demand
interface. This is an abbreviation for the existing dependent observation
interface, not a new runtime object.

The actual source argument is one section of this open input frame. The domain
`H_c` is not restricted to that section, successful invocation, or Return.

### 3.2 Local alternative declarations, not a whole-Call oracle

At the generic operator declaration, retain every original alternative's
actual declaration address and complete interface. A declaration `j` has:

```
Delta_j(h)                  original ordered local telescope
P_j(h,delta,inputs)         original input/guard/license evidence
A_j(h,delta,inputs,o;z)     original whole-tuple relation and its witness
D_j(h,delta,inputs)         independently declared COMPLETE output contract
local_type_j               the declaration's local output typing law
```

Its typing law has the precise shape

```
local_type_j :
  P_j(h,delta,inputs) -> A_j(h,delta,inputs,o;z)
  -> Mem(D_j(h,delta,inputs), o).
```

Every parameter and result occurs at its original scope. `inputs` may contain
the predecessor observation of a W clause. It must contain that predecessor's
original typed input/guard evidence when the primitive requires it. Mere
membership of a predecessor in the Call is not substituted for such evidence.
An output-changing clause retains its own domain action and output-dependent
provider/world/future interface. A source-independent schema may be
instantiated at this source use; it may not require the conclusion
`C0(c)` or an unprovided whole-source preservation law.

These are precisely the existing L1 primitive contracts. Their meanings and
witnesses are kept, not guessed from effect rows. An opaque declaration is
permitted; an unspecified predicate with a promised result endpoint is not.
The construction below is uniform in these declarations: no new choice of W
or Z, no enumeration of observations, and no assumption that their domains
are empty is needed.

The source kernel's complete clause signature is part of its declaration.
When forming its use, copy the complete signature, not a list of arms selected
by a successful query. An absent signature is not an empty signature.

## 4. Definition: a dependent union of complete result contracts

For complete contracts `D_j` over the same incoming frame, define their
scoped union using the existing union and scoped-binding clauses:

```
Mem(Join_j D_j, h, o)
  = sum over the original arm addresses j,
    with delta and inputs bound at THAT ARM'S original positions,
    of (P_j(h,delta,inputs), Mem(D_j(h,delta,inputs),o)).
```

This notation keeps the whole tuple, not just its ordinary value/effect
projection. In particular, its output future interface is the dependent union
of the actual branch's future interface. It does not reuse another branch's
future proof. The arm address is proof/source incidence, not a runtime sum tag.
For fixed-schema input/output aliases the same fields are shared, not copied.

There are explicit introduction maps `inj_j` and a case eliminator. Both are
just the existing logical union/scoped-binding constructors. They preserve
all operand identities and the complete dependent evidence. They do not
identify two different witnesses just because their observation projections
are equal. The union can be a finite graph of references to opaque/infinite
families; it need not enumerate their members.

The binder order is essential. `h -> (j,delta,inputs,...)` is a dependent
elimination under `h`, never `(j,delta,inputs) -> all h`. The generated graph
is built before events, while these variables remain underneath their
original event binders in its interpretation.

## 5. Definition: complete Call from its constructors

### 5.1 Structural constructor

For actual source callee code `n_f` and an admitted whole carrier `kappa`, put

```
S_c = Bind(n_f,
  (v,U,r,current_world) => ExecuteCallable(v,U,r,current_world,kappa)).
```

This uses the original Bind and ExecuteCallable relations and their full
observation witnesses. Its suffix includes receipt, the actual U's entry,
body, designated consumers and invocation return. It does not install a
Value entry or a Pure role on the supplied callable. Callee-pending and
receiver-pending suffixes remain distinct. Let `D_s` be the complete Bind
contract formed from the callee contract and the checked Function's complete
receiver-result contract, with the original dependent port maps.

The structural typing map `type_s : S_c(h,o;s) -> Mem(D_s,h,o)` is NOT an
input to source elaboration. Section 7 constructs it for this actual source.

### 5.2 Independent clauses and full operation membership

Define the new complete Call witness family by these constructors:

```
Struct(s)             where s : S_c(h,o)
Z(j,delta,p,z)         where p : P_j and z : A_j(h,delta,(),o)
W(j,q,delta,p,w)       where q : Call_c(h,x), p : P_j,
                            w : A_j(h,delta,x,o)
```

Equivalently the exhaustive generic alternative constructor is

```
Arm(j,delta,q_1,...,q_n,p,z)
```

where the declaration fixes the finite original predecessor-reference list
and its dependent telescope; the q_i fill exactly those references, and p,z
are the original primitive premises and output relation evidence. Z has no
predecessor and W has one. An opaque independently declared arm can occupy
one atomic declaration with its entire original interface and witness family;
it is not forced through Struct. Universal future obligations remain inside
that original interface, not new recursive universal premises on Call_c.

Use W's finite positive closure only when the declared operator has W
closure. A declared non-iterating arm is used once, not silently changed into
iterated closure. The typed reference graph retains those distinct roots.
Existing primitive guards and evidence remain exactly in p,z,w; no extra
output-success test is added.

This defines the missing composite operation from its declared clauses. It
does not take an already formed `Call_c` operation or its typing as a premise.
The new source use is the scoped instantiation of this generic declaration.
Its arm-to-root and root-to-source incidence are IF-Insert followed by IF-Use.
An independently fixed old root needs its actual constructor identification;
this definition is not a cast from any arbitrary old predicate.

Define the synthesized complete result contract to be

```
D_call = Join(D_s, all original D_j at their original scopes).
```

The independently interpreted ordinary descriptor conjunct is still present.
The retained complete constrained root uses BOTH `Call_c` and `D_call`.
Section 8 proves `Call_c -> Mem(D_call)`, rather than defining descriptor
membership to mean `Call_c`. Consequently that conjunct discards no generated
or independently licensed Call witness.

**No guard trick.** In particular, do not replace a Z or W output with
`A_j(...) and Mem(D_s,o)`. An alternative whose own contract differs from
`D_s` is retained through its own injection into `D_call`.

## 6. Definition: the source-owned demand and formation rule

### 6.1 Parameter and application descriptions

Reuse the existing Parameter declaration `A_f` and actual registration at
`d_f`. At c's original source description scope, introduce the result/effect
holes required by the Application rule program, with complete descriptive
sorts and their original free-dependency telescopes. A native row number
alone does not determine this telescope. No actual returned provider/world,
response or body witness is moved into a description binder.

Let `J_a` be the argument's complete declared carrier interface. Form `R_i`
using the existing complete computation descriptor constructor, with ordinary
result-description hole `B_i`, invocation effect-description hole `E_i`, and
its typed observation interface. A Return port binds its actual value/provider
and current world; a Request/pending port binds its actual packet, response
and raw suffix instead, without an invented returned value. The future port
is a dependent family over that actual output and the original compatible
extensions. Forming these binders is not choosing any of their inhabitants.
All original K/D, authority, path and hard-envelope predicates remain in the
complete descriptor. The holes are descriptions, not alleged proofs of those
predicates. This is not reconstruction of R_i from four native scalars.

The new demand constructor is

```
F_c = FunctionDemand(J_a, R_i, IF_c).
D_Fc = independent complete checked challenges for (J_a,IF_c).
P_Fc = the complete observation contract R_i at that same challenge.
```

`IF_c` is built from the actual source ports and full declaration/reference
interfaces by IF-Insert/IF-Use. The full checked challenge formation uses its
original context, other bindings and checked whole carrier. Neither actual-U
acceptance nor invocation-output safety is a challenge-formation premise.

Function membership is the existing contextual membership at these interfaces:
each actual decomposition must accept every such challenge and satisfy `R_i`
on every complete/pending observation and compatible future development.
Thus FunctionDemand completes the source descriptor's formation, not a new
callable-membership axiom or runtime wrapper.

The Application generates its original same-value bound `A_f <: F_c` at the
actual checking occurrence. In a symbolic source derivation the local inclusion
witness is a parameter of the generated constraints. It is not manufactured
from native query success. This is the ordinary inference obligation on the
unknown formal, NOT an additional premise asserting that the whole Call is
already well typed.

### 6.2 Gen-Call-Syntax: use the actual argument constructor

The formation rule is

```
actual Apply c = Apply(Name u_f, Integer a k); Resolve(u_f,d_f)
actual unannotated Value Parameter d_f; Parameter/Name derivation at d_f,u_f
Integer Literal derivation at a,k; Result and Reify/Delay derivations
complete demand F_c and actual checking occurrence
complete instantiated operator declaration and source-reference graph
-----------------------------------------------------------------------
Gen-Call-Syntax(c):
  original beta=(d_f,R_f), callee lexical use, actual argument-source use,
  checking occurrence, invocation and complete-Call output ports,
  ElimOrigin, and the complete dependent Call rule program
```

The new argument premise is the actual Integer Literal constructor, with its
`Data(a,Value(Int),...)` conclusion. For this source k=1. This is the selected
Name/Integer extension of the old Name/Name Gen-Call-0 spine; it does not
fabricate an argument lexical resolution. The old source constructors remain
available with their original domains and premises.

More precisely, extend the original formation judgement by this new
constructor, using the argument coordinate

```
SourceArgumentUse = NameUse(actual lexical derivation)
                  | IntegerLiteralUse(actual Integer literal derivation).
```

The old Name/Name constructor embeds with NameUse unchanged; every other old
constructor is retained unchanged as well. IntegerLiteralUse is admitted by
this new formation rule only at the resolved unannotated Value-formal seam
displayed above. It introduces no case for other non-Name data constructors
or computed callees. It cannot be projected to a nonexistent lexical witness.
The `OriginalGenCall0` request for c is discharged by this extended formation
judgement, not by a cast to the old Name-only input record. Its Rust input
interface must be updated at the owning definition when implementing this
case; the current `ArgumentLexicalUse` enumerator is not that implementation.

The formal shared root, immediate invocation position, whole-Call result
position and result-latent positions retain distinct roles even if a later
representation uses the same native term. Source-owned seed/exposure records
use the existing policy at their actual lexical/checking occurrences; they
create no dynamic receipt or authority. No proof of final ownership/coverage
is asserted by the static record alone.

## 7. Actual derivation of the structural `f 1` branch

All the following proof construction is uniform in the original typed body
environment and the generated complete inclusion witness.

1. The existing source-owned Strict Lambda rule introduces `I_f` before its
   challenges. For every independently admitted outer challenge, its proved
   same-frame entry law gives the actual post-Force/rebind binding
   `ValueBind(Empty,d_f,r_f,A_f,entry_origin)` on Return. On Request/divergence
   it retains the pending suffix and manufactures no body binding.
2. Resolve and Name select that SAME binding. Result returns the same `v_f`,
   actual provider and current world. From its A_f membership and the actual
   generated same-value inclusion witness derive membership in F_c. There is
   no instantiation of the lambda-bound formal.
3. Literal at a constructs the original Int primitive value k (k=1 here).
   Result forms `Return(k)` at its actual port. Its complete local typing law is the
   primitive/Return law. Reify at the Application's original argument port
   forms `kappa_a = Delay(Return(k))`. Inert formation has empty lexical
   capture; designated execution is proved by the same closed Literal/Return
   derivation at EVERY independently compatible future demand. The proof is
   a family under those demands, not a selected successful execution.
4. Keep the full `J_a` as well as that actual section. The printed
   `Comp(empty,Int)` does not identify J_a with the single returning carrier:
   all carriers admitted by its complete contract stay in the open slot.
   For an arbitrary h in the open frame, construct the checked challenge
   from h's OWN carrier-admission field, original punctured context and source
   port maps. Step 3 constructs that field for the source diagonal; it is not
   substituted for another carrier's field. This construction uses neither
   acceptance by v_f nor its output safety.
5. Eliminate F_c membership. For EVERY genuine `Act(v_f,U,r)` and each such
   independent challenge, obtain actual acceptance and the full `R_i`
   observation proof. Keep U, its entry/role, current world, receipt, response,
   raw continuation and output-dependent future fields from THAT elimination.
6. Apply the existing Bind constructor to the Name/Result proof and this
   receiver proof. On the actual Name Return branch it binds that same tuple
   and uses the receiver proof. Before that Return it retains the original
   callee pending prefix/suffix. Within receiver execution it retains the
   receiver's pending suffix. No argument receipt is replayed and no latent
   result is forced by inspecting its type. This constructs `type_s` at D_s.

For finite prefixes the proof follows the actual Bind cases. For future
validity, fix an arbitrary compatible original extension and apply the same
hereditary Name/carrier proof and Function elimination at that extension.
This retains `forall history; ...` under its original binders, rather than
choosing a history during elaboration. Nothing here assumes that f is a
source-known closure, total, pure, or Value-entry.

## 8. Complete-Call typing theorem and proof

**Conditional constructor theorem.** Fix a source occurrence in the selected
Name/Integer domain, its original binder tree and declarations, and one lawful
joint assignment at those scopes. Given its actual typed body environment,
the local constructor laws of sections 2-3, and its generated same-value
inclusion witness `A_f <: F_c`, for every independently valid original frame h,
observation o and full witness q of `Call_c(h,o)`, construct
`Mem(D_call,h,o)`. Neither `C0(c)` nor `TypedCallCert(c)` is an input. This
statement quantifies over satisfying assignments; it does not assert that
the open generated constraints have such an assignment.

Define its proof by constructor elimination:

```
type_call(Struct(s)) = inj_s(type_s(s))
type_call(Z(j,delta,p,z)) = inj_j(delta,p,local_type_j(p,z))
type_call(W(j,q,delta,p,w)) =
    inj_j(delta,p,local_type_j(p,w))
type_call(Arm(j,delta,q_1,...,q_n,p,z)) =
    inj_j(delta,inputs_j(delta,raw(q_1),...,raw(q_n)),p,
          local_type_j(p,z))
```

Here the shorter Z/W injections suppress their original inputs coordinate.
`inputs_j` is the declaration's actual predecessor/operand substitution, not
a newly selected tuple. For each predecessor reference q_i, retain its exact
raw observation, dependent scope map and existing typed input/guard evidence
in p. Where the original input is a typed Call-result reference, recursively
construct `type_call(q_i)` at q_i's own original telescope and use precisely
the declaration's existing input checking map retained in p. A union
membership proof alone does not supply a different primitive's operand type
or its guard. Any other required typed input is the original evidence already
retained at that reference; it is not manufactured by this recursion. Thus
each required input is either retained or constructed by the actual declared
consumer at its own scope, before applying the original `local_type_j(p,z)`.
This handles any declared finite predecessor list, including zero references
and non-iterating arms, with no strengthened guard or added closure case.

In the W case, `p,w` retain the original predecessor `raw(q)` and its
required original typed guard/input evidence. They do not substitute the
structural branch's provider/future certificate for the new output's one.
Any original additional premises of the clause are eliminated at their own
positions. Positive predecessor occurrences preserve the original derivation
by structural recursion; no universal future quantifier is moved into the
positive-closure operator. Primitive future/domain laws remain the actual
local laws under their original event binders.

Every right-hand side is an introduction of the existing complete union;
every input proof is either constructed in section 7 or supplied by that
independent primitive's own local law. This proves the theorem for all
constructors, including every declared Arm, unanchored Z and arbitrarily
long finite W chains.
It never chooses an arm to establish a universal result.

**Closing the actual Lambda, conditional on that assignment.** The proof is
uniform for every body binding
obtained by the already selected Strict entry rule. Use it as that rule's
body premise, with `R_L` equal to this complete body rule program at its
original event telescope. The resulting source closure has
`Strict(I_f, formal:A_f, R_L, IF_L)`, retaining the outer entry effects as well
as the body Call. This is a complete source derivation under the ordinary
generated local bound `A_f <: F_c`, not just a diagram for a hypothetical Call.
No proof for an outer Request/divergence branch creates a body binding; the
existing entry rule instead keeps its original pending body suffix.

**Unestablished satisfiability witness: the exact scope obstruction.** The
assignment `A_f := F_c` and the claimed nonempty identity-closure instance are
withdrawn. Reflexive inclusion is lawful only after both sides are proved to
be the same descriptor at the same scope; it cannot solve a dependency/scope
obligation by itself. The selected constructors establish the following:

- Source Generalize section 3.3 places
  `Desc(C,d_f,ValueEndpoint,sigma_f,Delta_f):A_f` before the Lambda challenge.
  It permits a body inference declaration at its owning invocation telescope.
  The source-owned Lambda section 4.1 likewise places `A_f,I_f` before
  challenges and `R_L` at the post-Force/rebind telescope.
- Section 6.1 forms `J_a,B_i,E_i,R_i,IF_c` at c's original description scope,
  without selecting actual output fields. Application_N section 4, Demand-N,
  places its demand/result/effect descriptions in `Delta_c`; it supplies no
  equality with `sigma_f` or lifting map to that earlier scope. Its section 5
  expressly separates formation from inhabitance.
- IF-Insert/IF-Use are formed before observations but retain every original
  dependent substitution. The complete Call frame in
  [source-interface construction](2026-10-08-call-source-interface-construction.md)
  section 4 includes `IF(CalleeRef_e)` and its whole interface;
  the selected Name interface references `A_f`. Static formation alone thus
  does not establish that all descriptive dependencies of `IF_c` exclude
  `A_f`, or that its event-indexed fields occur only bound inside the demand.

The missing law is at Parameter/Application description formation and its
IF-Use substitution: exhibit one lawful pre-challenge descriptor telescope
`Gamma_desc` containing the original `A_f` and all free dependencies of
`J_a,B_i,E_i,IF_c`, show that no EventField or actual runtime field is free in
the four source/native argument-value, argument-effect, invocation-effect and
result-value coordinates, and show every body event uses the restriction of
that SAME `F_c` through its original scope map. For this identity assignment
one must also show that the complete definition of `F_c`, including `IF_c`'s
reference dependencies, does not depend on `A_f`; otherwise substitution is
recursive rather than reflexivity. None of these conclusions follows merely
from the declaration order printed in section 6.1.

The native source owner allocates Parameter/expression endpoints once in
`candidate_source.rs` and traverses Lambda/body at the same numerical level;
`shadow_apply.rs` forms the four native demand coordinates. These facts do
not prove the required complete source dependency or event-restriction law.
No impossibility or source counterexample is claimed. The conditional theorem
and conditional Lambda closure above retain their original generated inclusion
premise at c's scope. Source satisfiability and the parent source/native gate
remain OPEN; no caller is restricted to identity or purity.

**Evidence retention.** Erasing the newly added type/placement witnesses
recovers the same structural witness or original j,delta,p,z/w and every
actual predecessor reference q_i. This is a literal projection, not equality
after observing
only the returned value or effect support. Induction preserves every
original member of the declared constructor family. No statement about a
different unspecified historical predicate is inferred from this projection.

**Dependent actions.** Rename/restrict every original operand and telescope
once. Each constructor above commutes with this operation by the existing
local action laws and union constructors. In particular an EventField remains
under its Event; the older Parameter description is not freshened for an
inner use. This supplies the local Call rule's source transport, not the
entire compiler Generalize or public-principality theorem.

**Non-circularity.** D_call is assembled from independently interpreted
contracts before observing Call_c. It is not defined as the set of this
program's successful runs. The implication from Call_c to D_call was proved,
so retaining the independent descriptor conjunct does not silently filter
any branch. Primitive laws cannot contain the missing whole-Call theorem.

## 9. One implementable elaboration, with existing owners

The source generation result is an OPEN constrained rule program and a
constructor derivation schema. Given genuine witnesses for its generated
constraints and its actual typed environment, the schema constructs the
complete typing proof above. Generating the schema is not solving its
constraints and must not return a closed `TypedCall` certificate.

For the selected new Name/Integer seam, use the existing source traversal,
with all old constructor cases retained:

```
Parameter: retain existing registration and its full source interface
Name:      reference the same registered endpoint and source binding
Literal:   apply the actual primitive/Result construction
Apply:
  Reify the actual argument under its source argument port
  form FunctionDemand and emit the ordinary complete callee bound
  form Bind/receiver source spine and instantiate ALL declared arm refs
  construct D_call by scoped full-contract union
  emit Gen-Call-Syntax and IF-Insert/IF-Use at the same source occurrence
  retain the complete rule program beside its existing native recipe
Lambda:    use this body root in the already selected Strict construction
```

The interfaces/constructor applications are a finite source/constraint graph,
with references to complete primitive families. No model search, per-carrier
enumeration, fabricated proof token, empty default contract, or duplicate
provider representation is necessary.

Ownership at the baseline:

- `crates/yu-hir/src/module/local_source.rs`: actual Lambda/Parameter/Apply
  nodes, resolution, argument identity and lexical scopes.
- `crates/yu-solver/src/candidate_source.rs`: Parameter registration, source
  traversal, actual literal/Name bounds, LambdaRecipe and ApplySourceInput.
- `crates/yu-solver/src/shadow_apply.rs`: the existing native Apply demand and
  the distinct argument/callee/invocation/application effect positions.
- `crates/yu-solver/src/candidate_call.rs`: borrow the actual source/native
  incidence. Its current PendingCallConstruction is not promoted to evidence.

When the source result is checked against a chosen ordinary result/effect
presentation, retain the exact complete root. Union elimination reduces a
check on D_call to checks at the actual constituent contracts and their
original source positions. Successful checks must use the existing local
checking constructors. Merely printing the union's value/effect projection
is not a proof of those checks or of latent-interface compatibility.

## 10. Exact remaining compiler obligations; not missing Call definitions

The construction above does not establish that the CURRENT native Function4
implements the new complete source rule. In particular:

1. Construct and retain the complete primitive/source interface references at
   their real owners, rather than deriving them from endpoint equality.
   The existing source handles suffice for locations, not for semantic truth.
2. Interpret the ordinary native demand/result/effect endpoints as projections
   of the SAME complete constrained Call root and its original scopes. Prove
   both source/generated directions for one joint assignment.
3. Check every independently declared arm in that projection. Current Apply
   emission adds callee and invocation effects to the application effect; it
   does not by itself show that every separate arm's result/effect/future
   constraints are represented. An arm already covered by an inherited hard
   envelope needs its genuine local inclusion; an independent contribution
   must not be silently dropped. Whether more native constraints are needed
   is an implementation/representation question, not a Call-typing axiom.
4. Preserve this complete rule program at source Generalize, replay/extrusion
   and eventual native discharge. The existing BOUND theorem can be applied
   to the generated complete callee edge; Function4 erasure alone is not its
   converse and does not prove public principality.

The relevant source typing theorem is under the ordinary generated local
constraints, not under a new premise called "the whole Call is safe". No
claim of native satisfiability, production acceptance, all-source completeness
or public principal output is made by forming this open program.

## 11. Review and integration status

This file is the constructive mathematical work, not a completed independent
review. The producer's checks include: no whole-Call proof input; no invented
argument Name; no actual-provider selection during description formation;
no source-diagonal restriction; no borrowed future certificate for another
arm; no post-hoc structural-output guard; no closed proof from open constraints.

The initial independent compiler_referee/spec_auditor review identified the
generic Arm proof case, an overbroad DataUse domain, and an unestablished
same-scope satisfiability witness. One batched repair added the actual Arm
elimination, confined the new case to resolved unannotated Value-formal
Name/Integer, and withdrew the witness while exposing its exact scope law. A
fresh compiler_referee and spec_auditor delta review passed those repairs.
This independently reviewed conditional constructor theorem does not establish
source satisfiability or the parent source/native theorem, which remains OPEN.
No production code, test expectation, public type language or cutover status
changed. Shared task/laboratory synchronization is owned by primary integration.
