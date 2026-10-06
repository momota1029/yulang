# Initial punctured contexts by simultaneous source generation

Date: 2026-10-06
Status: Research construction and conditional local inversion; compiler-referee review completed with no findings
Implementation authority: none
Baseline: `763ad96d4576ee6e2672c0cc35125e79c89fe955`
Lease: this progress note only; no compiler, authority, shared-status or Git changes

## 1. Result

There is a useful construction before an independently completed context
typing judgment exists. Generate one **open, whole-tuple context relation**
from the punctured source graph. Preallocate all source-owned bindings, visit
their definitions simultaneously, and leave the two designated holes rigid.
For source-owned closures, delays and saved suffixes, generate open descriptor
terms and their local constraints. Do not require their closed semantic
membership after plugging the tested callable. Ordinary independent semantic
imports instead contribute their already interpreted membership and joint
world constraints as leaves.

This removes a completed `TypedContext` premise from the *generation rule*.
The context's source-owned environment is an output of the same generation,
including aliases and captures of either hole. It does not make the remaining
local source rules true by definition. The construction has an exact
inversion theorem relative to independently interpreted descriptor operations,
P profiles and imports. For the representation-preserving ordinary Call,
the source elimination itself constructs its dependent receipt/entry schema:
it need not consume an unexplained supplied `ArgOpen` certificate. The actual
callable's parameter entry instantiates this schema only during later plugging
and execution. Original profile interpretation is a separate input from the
P lane. General annotations, handler patterns and source-state transitions
have their own explicit cuts when they occur. These cuts cannot be replaced
by another predicate called context well-formedness.

Consequently whole-tuple constraint generation does define a query-independent
**source seed schema**, relative to fixed local rules and semantic imports.
Its satisfiability is a different question. Its equality with the approved
complete production admission is a third question. This note constructs the
schema and its source-owned structural seed kernel, and identifies the
independent interpretations required to turn its witnesses into original
initial challenges. It does not declare the complete production A gate closed.

The holes are exactly those of concrete compatibility §8:

```text
Gamma; Sigma |- C : (box_f : T_checked, box_a : I_argument) => I_result.
```

`box_f` is the callable hole. `box_a` is the argument **code/carrier** hole,
not a second callable or an ordinary eagerly evaluated argument value. Neither
belongs to Gamma's semantic environment. Their actual fillings are not
premises of the open context derivation. Actual provider role and entry may
be supplied later for execution, as in the existing rigid-hole schema.

## 2. Governing sources and scope

The source judgments and interpretation used here are:

- typed computation core §§2–3 and 6: finite derivation graphs, `(I,d,n)`,
  the two source interface tags, inert introduction, source-designated
  consumption, parameter entry and constructor equations;
- typed core §7: independently interpreted same-decorated-value checking,
  distinct executable conversions and preservation of actual entry;
- typed core §9: whole argument, body and complete call are different ports;
- ordinary computation semantics §§2–3: the one current configuration,
  invocation entry, state-threaded bind, live resumed state and raw suffixes;
- source interface adequacy §2: complete immediate, latent and future-use
  observations at the original assignment;
- source contracts §§2–3.7: active constrained-root interpretation, separate
  admission, local descriptor typing lemmas and Option 2 root alternatives;
- source-indexed callback realization §§2–4: the finite immutable reference
  envelope, shared witnesses, constructor images and initial certificates;
- concrete compatibility §8: two rigid holes, open captures, semantic imports,
  current worlds and the qualified source State/reference boundary;
- Authoritative inferred Function call views §§1–5: inference from the shared
  declaration/definition/use component, no dependence on pending Q, actual
  callable preservation and the still-open exact source judgments;
- the approved production Function-denotation Option A and membership
  Option 2, reached through `notes/design/INDEX.md`.

The worked constructor envelope is the existing finite ordinary immutable
graph with literal, name, lambda, operation, reify, result, eliminate, Call
and Bind. Representation-preserving local checks are included as the existing
semantic propositions. The method does not exclude other source programs.
It lists the additional local cuts needed for them instead of imposing a new
source acceptance policy. No new syntax, carrier, profile rule, adapter or
solver operation is introduced.

## 3. Inputs and the one original tuple

Let `B` be the resolved finite punctured source graph, including the existing
source binder tree, declaration references and the distinguished application
occurrence `c_star`. Hole references are proof notation for puncturing existing
source, not new Yulang syntax. Preserve all occurrences of one source binder,
including references from closures, delays and continuation suffixes.

Preallocate a root `r_b` for every source-owned binding or expression node.
Each root has a symbolic source interface `I_b`, inert descriptor `d_b`,
designated consumer `n_b` and its original scoped endpoint coordinates. The
symbols name variables of the existing source judgments; they are not solved
types or new public type constructors. For recursive references, allocate once
and emit a back reference. A Name never creates an independent provider.

The global tuple contains:

```text
X = (xi, original source scopes and identities,
     all I_b, d_b, n_b and descriptor/root references,
     imported joint roots rho and their original contracts,
     two rigid hole references H_f and H_a,
     current source world C_0 and its live owner/view incidences,
     original slot/profile input P_beta,
     result/rebind paths, continuation references and local witnesses).
```

`xi=(nu,K,D)` is shared throughout. A constructor's local witness remains at
the original scope inside every rigid binder on which it depends. An operand
shared with a capture, another binding, a continuation or an admission record
is not existentially hidden separately at each use. The relation is projected
only after the joint context and seed record have been assembled.

For a complete production proof, the ambient descriptor universe is the
approved Option A basis. It may contain members with no source constructor
body. The source-owned descriptor terms below inhabit a source-generated
part of that universe; ordinary imports are not restricted to that part.

## 4. Local generation rules

Write the generation judgment

```text
Delta; H; R |- e => (I_e,d_e,n_e ; Phi_e, J_e).
```

`Delta` supplies independently interpreted declaration/import contracts. `H`
is the two-hole typing context. `R` is the registered source root table.
`Phi_e` is a relation on the one tuple X. `J_e` records original source
incidences produced by this occurrence. It contains static source references,
not automatically live grants. Generation emits `Phi_e`; it does not assume
that an assignment satisfying it has already been found.

All child predicates are conjoined on X. For a finite shared graph, this is
one traversal of registered definitions, rather than recursive duplication
of captured bodies. Ordinary positive execution back references retain the
existing finite-derivation interpretation. Source typing constraints at
unknown recursive interfaces are retained equations; this note selects no
recursive inference or semantic fixed-point convention for them.

### 4.1 Hole, literal, independent import and Name

**Hole.** For the designated callable reference, generate the hypothetical
source interface for `T_checked` and `d=H_f`. For the argument reference,
generate `I_argument` and the formal data/consumer pair `(d_a,n_a)`, indexed
by H_a and related by Normalize at that interface. The whole argument code
is n_a; the inert carrier is Delay(n_a), not a prematurely evaluated value.
Neither rule emits
`DescMem(T_checked,actual_callable)` or semantic membership of the actual
argument filling. The hypothetical interfaces license ordinary open typing;
they do not assert inhabitants, execute code or discharge Q.

**Literal.** Generate its existing ordinary literal interface, descriptor and
local primitive relation. This relation retains any genuine declared local
alternatives. No whole-Function comparison is used.

**Operation name.** Copy the independently interpreted original operation
declaration instance, payload parameter interface, native delimiter and
designated result consumer. Generate its inert operation descriptor and
Value(Function) interface using those same declaration coordinates. Its
completed invocation uses common receipt/entry and then the declaration's
consumer after native return. Producing the request thunk emits no request;
only the source-demanded consumer exposes it. No declaration witness is
invented by matching an operation-family row.

**Independent semantic import.** An import name refers to its original
descriptor/root in `rho`. Its supplied local contract contributes independent
descriptor membership at that root. When imports share operation instances,
roots, continuations or live state, retain their supplied **joint** relation,
not a product of independently chosen leaf witnesses. A semantic import is
allowed to be an Option 2 provider without a source body.

The import premise has this exact domain:

```text
Imp_Delta(rho,C_ext;xi,w_imp):
  original imported roots satisfy their independent descriptors;
  their operation-instance/endpoints, scope and retained K,D agree;
  shared roots and continuations have the same original witnesses;
  imported live frames have independently justified current ownership,
    receipt/profile/path incidences and source-compatible activation order;
  expired activations have no live incidence.
```

This is a genuine semantic leaf relative to the supplied import interpretation.
It is not a new definition of all admissible worlds. In particular it may not
certify a source-owned closure containing H_f as a **closed** imported member,
or supply arbitrary state transitions. An external semantic free-variable
world is not required to be a closed-program reachable world.

**Name.** If source resolution maps `x` to `r_b`, emit

```text
I_x = I_b; d_x = name(r_b); n_x = Normalize(I_b,d_x).
```

Retain that root's original dependent references. A hole reference remains a
hole reference through every alias. Capturing a Name copies the root reference
and its original typed source position. It creates neither a fresh provider
nor a new receipt or activation. Identity transport at an already interpreted
typed path is the ordinary same-root identity; completeness of the inventory
of applicable profile positions is the separate P input.

### 4.2 Normalize, Lambda and Reify

Use the disjoint existing clauses:

```text
Normalize(Value(A),d)         = result(d)
Normalize(Computation(E,A),d) = eliminate_p(d).
```

The second clause refers to the original designated computation port. It is
not selected by solving A to a thunk shape. For an unresolved source interface,
retain the interface/tag equations rather than guessing its tag. Complete
raw annotation interpretation is an explicit cut in §8.

**Lambda.** Select introduction role from the existing source context before
body generation. An ordinary unannotated noncallback introduction selects
Pure; known callback context or a Function annotation supplies its established
Handler boundary. Keep receiver role separate from parameter entry. Generate
the ordinary parameter interface and entry skeleton by typed core §6, then
generate the body under its registered source parameter root:

```text
I_lambda = Value(Fun(P,Result(I_body)))
d_lambda = lambda(entry_P,n_body,captured source-root references)
n_lambda = result(d_lambda).
```

The displayed Fun is typed core §6's **body/result skeleton**. It does not
equate the complete call bound with Result(I_body). If a complete advertised
Function descriptor is required, add the ordinary complete lambda rule's
local obligations: the whole received argument, generated entry, current
post-entry body state, designated consumer and invocation return form the
same complete ExecuteCallable image. Generate the complete image and its
semantic bound constraint jointly with the body. The original role-indexed
descriptor and profile interpretation is an independent P/descriptor input
where it is not already provided by the known source contract. Body synthesis
alone does not derive that interpretation. This also applies to source-owned
lambdas other than the distinguished slot's P construction. No opaque
`LamOpen` premise is needed for the source-owned entry/image skeleton.

Conjoin the body's local predicates at their original scope. A captured hole
is a formal root in this open descriptor term. The Lambda rule has **no**
extra premise saying the filled closure is a closed member of its advertised
Function descriptor. Such a premise would put the target membership under
test back into the environment. Local descriptor typing of the completed
lambda, when required by another source boundary, remains an ordinary open
typing/realization lemma relative to the complete constructor images and
independent descriptor/P interpretations displayed below.

**Reify/explicit inert introduction.** Store the generated computation and
its lexical references without executing any prefix. Use the existing source
interface for the explicit introduction. Application and Bind results already
use the existing `Computation` interface and its consumer; explicit lifting as
value data has the distinct existing `Value(computation-data(...))` interface.
Do not invent a surface keyword or let endpoint equality choose between them.

### 4.3 Result, Eliminate and Bind

**Result.** Return the generated descriptor at the current configuration.
Descriptor identity and all dependent source roots are retained.

**Eliminate.** Refer to exactly the source-designated computation port and
its existing consumer. Its local realization obligation is the independent
typed path correspondence for this source elimination. It does not force
every latent descendant of the result. If that correspondence was not
generated by the existing source interface/tag rules, it is a true local cut,
not a reason to guess a path from solved type shape.

**Bind.** For `my x=r; b`, generate r, register `x:Value(A_r)` at its source
result binding, and generate b. Emit the existing whole Bind image with the
same result, current-state and suffix witness:

```text
d_bind = reify(bind(x,n_r,n_b))
I_bind = Computation(E_bind,A_b)
Return(v,C) >>= S = S(v,C)
Request(q,C,k) >>= S
  = Request(q,C,lambda(response,C'). k(response,C') >>= S).
```

`E_bind` bounds this existing image. No independently projected result/state
components are recombined. A request carries its original operation witness,
origin, K,D and raw continuation; the generated suffix is appended to that
continuation and resumes at C'. It is not evaluated at construction time.

### 4.4 Call outside the distinguished interaction

Generate f and a, allocate a single complete Function variable F at the
resolved callee/root scope, and emit the semantic rule:

```text
WF_Dec(F;xi)
VIncl(A_f,F;xi,e_f)
WholeArgCompatible(Result(I_a),CarrierContract(F);xi,e_a)
ReceiveSchema(c,F,original callee root,Delay(n_a),call view;xi)
CIncl(ExecuteCallableImage(n_f,Delay(n_a),F,e_f,e_a;xi),
      Comp(E_call,A_call);xi,e_out).
```

`VIncl`, `CIncl` and `WF_Dec` are the already independently interpreted
decorated semantic propositions of typed core §7, not new solver atoms. Their
quantification is over the same decorated values and complete joint behavior,
not one convenient callee value or successful trace. The image evaluates the
callee, inertly constructs the whole argument, establishes actual receipt,
uses the actual callable's entry/body/designated consumer and returns.

`WholeArgCompatible` is the existing independent complete whole-carrier
contract proposition, not a new syntactic acceptance test. For the same-value
checking fragment it is expressed by the existing complete interface
inclusion/membership predicates at the actual inlet, retaining the original
source tag and packets. Its interpretation belongs to the independent
descriptor kernel. It does not assert that a target-valid carrier fits an
unrelated actual callable; that domain inclusion remains a later obligation.

Construct ReceiveSchema by the source Call elimination itself:

```text
source-input(c) -> F.received-carrier, carrying Delay(n_a)'s original root;
source-complete-output(c) -> F.complete-call, under one call view;
receipt(c) precedes Entry(actual_provider);
Entry(Value(A)) = Force designated carrier port; Rebind to provider parameter;
Entry(Computation(E,A)) = bind the same carrier to provider parameter;
then provider body, designated result consumer, invocation return.
```

The mandatory received-carrier and complete-call addresses are typed by
Function elimination, not guessed from solved endpoint equality. As with
Gen-Call-0 in the predecessor, the source elimination fixes this immediate
correspondence even while F is symbolic. The schema's provider-parameter
reference is dependent on the *later actual producer*. It is not a source
binder invented for that producer and cannot change actual entry. The two
entry cases are precisely the existing source parameter tags; Value force
is followed by one typed result rebind, while retained entry carries the
same root without forcing it. The actual provider's supplied/generated
parameter binding instantiates the dependent reference later.

Transport uses the argument's original packet at those source-designated
positions, together with P's interpreted slot/profile, in the one current
call view. It retains origin, operation witnesses, scopes and xi; it does not
invent a correspondence for every latent descriptor child. P supplies the
complete inventory of applicable positions. Current dynamic activation is a
schema parameter until actual receipt; no runtime Receive, Flow, Observe or
capture grant is claimed at generation. On instantiation the existing
constructor-image typing/transport law validates exactly these source edges
in the actual invocation. This law is relative to independent descriptor and
P interpretations, not to the truth of Q.

Thus an `ArgOpen` wrapper is unnecessary for the source-owned structural
Call kernel. Its independent semantic contract constraint remains visible,
and an admitted executable adapter would require its separate actual source
derivation. The same-value schema does not settle arbitrary conversion or
annotation interpretations.

Local Calls through H_f are checked **hypothetically** against its formal
checked contract. No actual tested filling is installed. Such a body can
occur in an open containing closure. Whether it executes after plugging is a
later actual-behavior and domain-containment question.

For an unknown callee and callback literal, the Authoritative pre-body
callback-context contract still applies. This note does not silently select
Pure before the expected contract is available. Exact formation of that
expected context is a remaining source local cut; the known-contract case
uses the existing role-first B scheduling.

## 5. The puncture and PCInit rule

At `c_star`, do not generate the pending tested Function comparison or a
closed preservation premise for the plugged call. Replace precisely the
callee and whole argument references by H_f and H_a, retaining their
hypothetical source interfaces, the original static call occurrence, slot,
whole-carrier root, result/rebind path and the ordered surrounding suffix.
The context may still contain other source Calls, each governed by §4.4.

Generate every remaining source-owned binding and the surrounding descriptor
graph by §§3–4. Let `Phi_B^H` be the conjunction of those emitted local
relations, the unchanged independent original source residual, and independent
import leaves. Preserve the pending tested Q separately in the full proof
obligation; it is not a conjunct or assumption of Phi_B^H. This separation
does not erase or discharge that later query.
Extract `Seed_B(X)` by the source occurrence projections:

```text
Seed_B(X) = (beta,H_f,H_a,whole argument source interface/root,
             current C_0,argument and result/rebind paths,
             original context graph and source-root environment,
             ordered pending suffix,original scopes and xi).
```

The initial rule is:

```text
Gen(B^H) = (Phi_B^H,Seed_B)
P_beta has its original independent profile/position interpretation
X satisfies every displayed local source relation and import/world leaf
---------------------------------------------------------------- PCInit-source
Initial_source(Seed_B(X);xi).
```

Here `Initial_source` means the initial constructor of the existing
source-generated reference admission inventory, under its fixed independently
interpreted local typing rules. It is **not** defined to be complete production
A. The first line constructs a schema even if the third line is unsatisfiable.
The third line is explicitly expanded by the local rules above; it is not a
completed “independently typed context” premise under a different name.

PCInit-source contains no actual checked membership of H_f, no execution of
H_a, no observed return and no success of Q. Source-typed argument code is
represented by its hypothetical interface and independent code derivation;
the hole need not return. A pure diverging whole carrier is not lost by a
return-only seed test.

When concrete fillings are later supplied, plugging replaces both hole
references **everywhere in the one graph**, including captures and pending
suffixes, preserving sharing. It does not freshly choose independent values
for aliases. The source-origin/code certificate for the supplied argument
must be independent of the pending callable comparison. A formal hole typing
assumption alone is not a certificate that an arbitrary actual code/carrier
satisfies that interface. The actual callable uses its own actual role and
entry; no target-membership preservation theorem is applied to the plugged
program. These are the existing rigid-hole restrictions.

The distinction matters: an open seed schema can exist under hypothetical
uninhabited assumptions. Actual challenge realization requires the actual
argument/source world witness; emptiness cannot prove annotation acceptance
or the intended domain inclusion. This is a realization condition, separate
from emitting the schema and separate from solving Q.

## 6. Worked hole-dependent binding

Take the existing derivation shape containing a source-owned open closure
`k = lambda x. call(box_f,result(name x))` and an independent imported value g.
This is proof syntax for an ordinary source lambda/application graph, not a
new surface term. Suppose k is retained by the context and the distinguished
application passes H_a to H_f elsewhere.

Generation allocates one k root and one H_f reference. Parameter generation
constructs `x:Value(A_x)` and its entry skeleton. Name x reads that original
parameter root. The body Call emits its local complete Function, whole
argument, path and invocation-image constraints against the *formal*
T_checked; k stores this open body and the H_f root. An alias `j=k` reuses k's
descriptor/root. The independent import g contributes its semantic membership
leaf and any joint imported dependencies.

The generated context environment is thus

```text
eta_open(k) = Closure(entry_x; generated body,[H_f])
eta_open(j) = the same k root
eta_open(g) = the independently supplied imported root.
```

No step asks whether
`Closure(entry_x;body,[actual_f])` is a closed member of the target-checked
Function. No step copies the same closure into two independent root witnesses.
Plugging actual_f changes both H_f references through one substitution. This
directly discharges the structural open-capture issue that a context premise
would otherwise hide. The body Call's immediate receipt/entry correspondence
is generated by ReceiveSchema. Its semantic constraints use the independent
descriptor and P interpretation; no additional closed semantic membership
requirement on k's actual filling is introduced.

If an externally supplied value itself contains actual_f by a relationship
not represented as the source graph's open hole reference, it cannot simply
be recast as k or admitted by a closed independent import leaf. Exact coverage
of such external worlds needs the original semantic import/world interpretation
and its open-substitution certificate. This note neither excludes such worlds
from production admission nor certifies them without that evidence.

## 7. Bidirectional local inversion

Fix the imported descriptor/world interpretation, P's original profile, and
every local side relation left in §§4 and 8. Fix the source binder tree and
the two-hole interface assumptions. Consider ordinary open source typing
derivations using exactly these interpreted constructor rules.

**Forward inversion.** A derivation determines its root interface, data and
consumer at each source occurrence. Read them into the registered tuple.
Literal and import leaves provide their original local witnesses; Hole uses
only the hypothetical interface; Name copies the resolved root; Lambda reads
its generated parameter, body and capture references; Reify retains its code;
Bind reads its joint result/state/suffix; Call reads F and its independently
interpreted whole-argument and image witnesses. Put every witness at the
source rule's original binder position. Each generated conjunct is exactly
that rule's side condition, so the one tuple satisfies Phi_B^H. The extracted
seed is the original punctured-context seed, with no actual hole membership.

**Reconstruction.** From one satisfying tuple, construct the source derivation
node by node. The source constructor chooses the same I/d/n equations.
Its displayed local conjuncts provide its side conditions. Hole remains
hypothetical and Name points to the registered original binder. Captures use
the same source references, so containing closures are open derivations.
For recursive source graphs the reconstruction is a finite derivation graph
with the same registered back references; no recursive source body is
unfolded merely to construct the graph. The ordinary execution interpretation
of positive back references remains the fixed finite-prefix interpretation.
No inference fixed-point result follows for unknown interfaces.

The two maps preserve the distinguished call, source scopes, one xi, imported
roots, sharing, typed result paths and pending suffix. They are inverse up to
the existing capture-avoiding fresh-label renaming and irrelevant proof
presentation. At original local existential scopes, retain the shared witness
behind projection. Do not derive inverse maps for projected marginals and
then assume they agree on a joined witness.

For Call, extract the independent contract/image witnesses and verify that
the derivation's immediate received-carrier and complete-call positions are
exactly those designated by source Function elimination. Its actual receipt
and parameter entry instantiate ReceiveSchema at the same actual provider;
they are not a fresh proof of Q. Conversely the interpreted source elimination
schema and the independent contract/image witnesses reconstruct that local
Call. A supposedly valid Call with no carrier receipt before entry would
contradict the existing common invocation equations, rather than represent a
second admissible source Call rule in this envelope.

This proves equivalence between the whole-tuple constraints and the **ordinary
open derivation envelope once its independent interpretations are fixed**.
It supplies the source-owned structural A kernel without requiring a completed
context typing input or opaque ArgOpen/LamOpen certificate. It does not prove
an independent P/descriptor/import interpretation whose concrete clauses are
absent, nor normalize arbitrary executable adapters or source-state forms.

## 8. Residual atoms and boundaries

The remaining obligations are localized as follows.

| Atom | Source-owned output already generated | Genuine input still required |
| --- | --- | --- |
| Original profile/position interpretation P_beta | Distinguished Call occurrence, shared contract root, static immediate invocation address, hole identities and original scopes | Exact applicable slot/contribution inventory and original annotation/protection interpretation; this is the separate P gate |
| Complete descriptor/role-profile interpretation | Generated lambda entry/body/result skeleton and complete image; Call's dependent received-carrier/complete-call/entry schema | Independently interpreted role-indexed Function and whole-carrier contract, P's original profile positions, and the constructor-image typing laws at those positions; Result(I_body) alone is not a complete bound |
| Designated elimination correspondence | Source interface tag, one known consumer occurrence, its referenced port | Independent typed correspondence when not determined by already admitted source interface/declaration rules |
| Annotation/declaration leaf | Original annotation occurrence, declaration identity, scopes and parameter entry table | Full annotation-to-descriptor/path interpretation; overlapping callback/Function annotation ordering where not already specified |
| Independent import/current external world | Original imported names/contracts and explicit joint identity references | Independent descriptor membership and joint original world/continuation/authority constraints for their semantic interpretation, including allowed production-only members |
| Handler source form, if present | Ordinary guard/arm/body source skeletons and outside-selected-handler order | Original pattern/coverage/typed handler premises and their complete shallow-image certificate |
| Source State/general-reference form, if present | Source identities and ordinary expression/capture roots | Selected source transition/world clause: State update as continuation restart, or the independently admitted general-reference operation and continuation/alias interpretation |
| Executable conversion, if required | Source boundary occurrence and before/after interfaces | Independently admitted conversion derivation with its source placement; representation-preserving VIncl/CIncl cannot replace it |

This table is exhaustive for the stated constructor envelope and explicitly
marks extensions. A local check's complete semantic inclusion can itself need
the still-open complete descriptor/admission interpretation; calling it an
ordinary `A <: B` obligation does not prove that interpretation. The table
does not permit a generic supplied `TypedCallCert`, `JointWF` or `TypedContext`
to discharge all source-owned evidence at once.

For an initial configuration constructed by a source prefix, generate that
prefix by the same rules and carry its open continuation/world through the
existing state-threaded constructor image. For an arbitrary already-current
semantic free-variable world, the independent import/world leaf is necessary.
Raw finite context syntax does not determine which external operation
instances, raw continuation handles or currently active receipts actually
exist. Treating all graph-shaped current states as legitimate or requiring
closed-program reachability would choose a new domain.

The source immutable constructor laws transport an already interpreted
world; they do not create permission. A saved suffix captures original code,
source references and K,D. On resumption it takes the actual current state and
same operation witness. It neither replays receipt nor restores an expired
handler or maker grant. For source State, no primitive shared heap/cell write
is inferred. These facts constrain reconstruction and prevent the world
leaf from being used to fabricate a source transition.

## 9. What is canonical, and what is not yet proved

For fixed local relations, `Phi_B^H` is canonical up to fresh-label renaming
and ordinary conjunction reassociation. The source graph fixes constructor
tags, operands, shared binder references, both holes and original scopes.
Even if source interfaces have multiple admissible solutions, the **relation
of all such solutions** is emitted without choosing one. Defining this
relation does not require an algorithm for choosing, finding or normalizing
solutions. Unknown definition components can be emitted simultaneously with
their ordinary interface equations. That is relational generation, not a
claim that an unknown recursive role is uniquely solved.

With the local interpretations fixed, define the source initial domain by
original-scope joint projection of satisfying PCInit-source tuples. This is
an extensional definition; effective satisfiability and principal projection
remain separate. It uses no pending Q, independently chosen port witnesses,
effect-position meaning of `never`, or output-support inference of authority.

Three equations must not be conflated:

```text
Generated_schema = ordinary open source derivations under fixed local rules

Initial_source = original source-base initial challenge rule

Initial_production = complete independent Option A/2 admission.
```

The first has the conditional constructive inversion above. The second
requires the independent descriptor/P interpretation and import/world
realization, with actual-provider instantiation of the generated receipt/entry
schemas. The source-owned structural context is generated, not supplied as
TypedContext. The third additionally
requires exhaustive original production admission and permitted semantic
provider developments. Source contracts §3.7 explicitly warns that positive
membership abstraction alone does not certify changes to admission-live
provider/history coordinates. No W/Z grammar or source-only production
membership policy is selected here.

Option 2 members can occur at independent descriptor/import leaves and later
provider developments without source-body derivations. The source schema
therefore does not force a source witness on every imported provider. It still
does not prove that every complete production challenge has such a source
context realization, or that every permitted production-only continuation
development is covered by the source seed. Those are production correspondence
obligations, not a consequence of the finite context traversal.

The two-hole construction also does not prove `D_checked subseteq D_actual`.
It keeps the actual callable out of target semantic environment membership
precisely so that this inclusion can be proved separately using its actual
entry and domain. Likewise the complete actual observation inclusion is a
later obligation. A source seed theorem does not select the full Function
inequality, principality or a compiler acceptance rule.

## 10. Verification and commit packet

Method budget: one simultaneous whole-tuple source construction and one
bidirectional ordinary-rule inversion. No numerical, fixed-point or finite
model checker was run: none would decide the missing original local path/world
interpretation. No compiler build, test suite or implementation edit was made.

Checks performed: governing-source inspection; explicit verification of the
two-hole distinction against concrete compatibility §8; constructor-by-
constructor coverage of the stated immutable envelope; witness/scope audit;
semantic-vs-source import audit; separation of generation, satisfiability,
plugging and production correspondence. These are author checks, not
independent mathematical review. Dependency hashes are reported in the
worker handoff and below, and must be rechecked by the integrating primary.

Exact leased changed path:
`notes/progress/2026-10-06-initial-context-source-construction.md`.

Proposed commit message:
`research: construct open source initial-context constraints`.

Claim class: research-only conditional source-owned initial-context kernel
construction and precise remaining interpretation/extension cuts; no complete
production A closure, production conformance, principality,
production correspondence or implementation authority. Shared-record deltas are
intentionally deferred to the primary: tasks/current, research queue, design
index and theorem maps should reflect that the aggregate context-typing
premise has been removed for the representation-preserving ordinary structural
kernel relative to P/descriptor/import interpretations, with the listed
interpretation and extension cuts still open. No new user decision is requested
or selected by this artifact.

### Frozen direct dependency SHA-256

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-10-02-source-interface-adequacy-theorem.md` | `6b8f95cfc2380508d500c447c82b64fd2c26fb32248e6fb3244314cc02023660` |
| `notes/design/2026-10-04-source-indexed-callback-realization.md` | `76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
