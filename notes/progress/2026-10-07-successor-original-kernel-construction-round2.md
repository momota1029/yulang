# Original owner/kernel construction, round 2: whole-contract lifting

Status: independently reviewed research-only candidate construction
Review: [round-2 compiler/spec review](2026-10-07-successor-round2-review.md); no findings; original semantic leaves remain open
Baseline: `ad514061de2792c374a4b5c224dff7f4772906e8`
Gate/method: ORIGINAL_ASSOC / SIG_RULES P2–P4; constructive local rule package
Exclusive leases: this note and `tools/research_successor_original_kernel_round2.py`
Semantic and implementation authority: none

## 1. New result, retained stop, and precise claim class

This round constructs a **local whole-contract lifting calculus** and proves
its conditional assembly and witness-retention theorem. Unlike the previous
assembly statement, it specifies how a uniform family certificate is built:
lift independently interpreted primitive contracts, then lift every positive
whole-relation constructor, finally introduce an original source-owned
incidence. Union builds one parent contract covering both complete children;
Bind and Call preserve the ordered relational image and pending suffix.
No pointwise selection of an association witness is used.

This is a candidate package for original-kernel rules, not a replacement
interpretation of `I_orig`, `Slots`, contribution sorts, or licensing. Its
original-coordinate embedding is an explicit typed relation into those
existing objects. Non-lossy witness transport is a separate condition from
existential assembly. In particular, the package never sets
`I_orig := image(assembly)`.

**No existing original semantic leaf is closed.** The theorem is conditional
on named local original-kernel sequents below. The constructive advance is
the reduction of the prior opaque P2/P3 assembly premise to a finite collection
of original primitive/constructor lifting laws, one precise source-owner
introduction, and a stated exhaustive original licensing decomposition. The
proof of compositional assembly is new; the existence of those laws in the
original kernel is unproved. This is neither a source counterexample nor a
claim that a new user decision is needed.

The executable probe checks the free candidate algebra, exact nested capture
and inert return records, coordinate coherence, and named shortcut mutations.
It cannot establish that the candidate algebra is the original kernel. It is
deliberately small; a larger enumeration would not establish the embedding.

## 2. Fixed source and independent premises

The source is exactly:

```text
my apply f = { my step x = f x; step }
```

The selected core correspondence is:

```text
lambda(f,
  bind(step,
    result(lambda(x, call(result(name f), result(name x)))),
    result(name step)))
```

`f` resolves to the outer formal, `x` to the inner formal. The final `step`
returns the local closure and does not execute its latent body. A later use
retains that same captured `f`. The Name computation for `x` in `f x` returns
the rebound value; it is not the whole carrier that entered `step`.

Keep the original source component, original binder tree, source upper `u`,
original typed output correspondence `p0`, provider roots and one shared
`xi=(nu,K,D)`. Event-local compatible extensions stay under their original
binders. All statements are pointwise in independently valid admitted worlds;
no nonempty world or admitted-row existence is assumed.

The complete family is the predecessor's already constructed relation:

```text
J_fx = J_f >>= ((actual_f,C) =>
  ExecuteCallable_X(actual_f,Delay(J_x),C))
```

It retains callee evaluation, whole inert argument, actual role/entry,
receipt/receiver, body, designated result consumer, invocation return,
finite pending prefixes, resumed current state and future returned-provider
uses. In the exact Name/Name cut the returning lexical operands require
lookup adequacy; this does not validate every conservative production member.

For the constructive theorem grant independent local complete typing
`Hcall` and the independently interpreted primitive/world/kernel meanings
used by source-contracts §§2.1–2.2. `Hcall` must not contain the desired
association hidden in a supplied complete profile. Source emission and
positive relation constructors are available conditionally under their
stated rules. Full production membership `Sat_A` and admission `Adm_A`
remain independently interpreted, with their actual full hard constraints.

Current directional protection is fixed:

```text
ProtectedVarAt(k,v,sigma,u) and SourceUpperUse(u,v,U,sigma)
  => NewProtection(k,u,outEff(U)).
```

Only that upper output receives this seed. Lower/provider protection neither
acquires it by backflow nor loses independently owned marks. The seed is
not contribution typing, a receipt, an event mark, or an actual role rewrite.
Callback literal B, annotation-local permissions and actual callable entries
remain unchanged. No Value-entry-implies-Pure rule is introduced.

## 3. Candidate semantics with an explicit original-coordinate embedding

### 3.1 Certificate sort versus original semantic sorts

For a finite typed relation presentation `E`, let `R_E` denote its existing
whole-tuple relation before `Pi`. A member retains challenge, observation,
source stage/view incidence and its local semantic evidence. Relation
membership evidence is not an original association witness.

The proposed proof certificate `L(E)` is a finite DAG whose node records:

- the existing relation constructor and ordered source operands;
- its original typed port and scope correspondences;
- the full non-child operand tuple, including actual provider/entry/consumer;
- every child certificate and every retained primitive evidence alternative.

This is metatheoretic proof syntax. It is not a new semantic contribution,
slot, carrier or runtime object. In particular `L(E)` cannot be cast to `c`.

Use the following names solely for obligations about the **original** sorts:

```text
Contrib_orig(c,rho;X)                original independently typed contract
CMem_orig(c,y,w;X)                  its complete whole-tuple membership
Own_orig(beta,s,u,p0,o;X)            original static owner/position evidence
Emb_orig(L(E),c,v;X)                certified embedding into that contract
Inc_orig(a,beta,s,p0,u,c;X)          original incidence, a in I_orig(X)
Cover_orig(a,z;X)                   unchanged original coverage judgment
```

These names do not define the original meanings or imply that the original
implementation exposes these exact fields. An eventual original kernel with
different presentation fields must prove the corresponding sequents on its
actual judgments. `rho` is an original typed interface at its existing scope;
it may differ across subnodes. Child scopes need not be equal to the parent
scope. Their **original typed maps** must be legal under the single binder
tree and joint assignment. Demanding one identical `s,p0` at every child
would invent a slot-sharing law; this package does not do so.

`Emb_orig` is a proof relation, not a function choosing a canonical witness.
It records a witness relation `B_E` between the entire certificate membership
fiber and original membership evidence. Its soundness law is:

```text
Emb_orig(L(E),c,v;X) and d : R_E(y;X)
  => exists w. CMem_orig(c,y,w;X) and B_E(d,w).
```

`B_E` retains each original local evidence leaf, origin, provider, scope,
dependency and stage map. It must not identify two original evidence
alternatives merely because `Pi(y)` agrees. The converse is required for
original witnesses represented by that particular contract, when a
witness-exhaustive representation is claimed. Existence alone needs only
soundness. The original relation remains present regardless of this image.

### 3.2 Exact candidate local introduction sequents

The proposed rules have the following additional original-kernel premises.
None is imported from successful `Q` or endpoint-ID equality.

**K-Leaf.** For each independently typed primitive contract at original
`rho`, including provider/import/annotation contracts and conservative
licensed alternatives, prove:

```text
PrimitiveRule_r at rho with its independently typed whole relation R_r
---------------------------------------------------------------- K-Leaf
exists original c,v. Contrib_orig(c,rho;X)
  and Emb_orig(L(r),c,v;X).
```

The local proof supplies a `B_r` for **every** primitive semantic witness,
not just a chosen returning execution. It also retains inherited original
license evidence as a payload. A source-only leaf cannot represent Option 2
extras; their independent contracts require their own K-Leaf proof.

**K-Image.** Let `C` be one fixed positive whole-relation constructor. The
ordered operands `z`, original typed maps `iota_i` and binding positions are
those in `E`, rather than inferred from erased endpoints. Prove:

```text
Contrib_orig(c_i,rho_i;X) and Emb_orig(L(E_i),c_i,v_i;X), for every i
TypedOriginalImage_C(rho_i,iota_i,rho,z;X)
----------------------------------------------------------- K-Image(C)
exists original c,v. Contrib_orig(c,rho;X)
  and Emb_orig(L(C(E_i;z)),c,v;X).
```

Its substantive semantic law is whole-relational image preservation:
for every original child membership tuple and **compatible joint** child
evidence used by `C`, the original parent membership has the same image
tuple and retains that exact child evidence and the original image witness.
The back law, if claimed, recovers those same compatible premises. This is
not a Cartesian product of independently projected port fibers.

The required instances are explicit:

| Instance | Required original lifting law |
| --- | --- |
| Whole union | One original parent contract represents both children; a branch tag retains every child witness. It does not choose a branch per complete family. |
| Conjunction | Retain both predicates on the same whole tuple and compatible joint evidence; no marginal recombination. |
| Return | Return the same descriptor/provider and current configuration; retain latent provider contracts without executing them. |
| Request | Retain declaration instance, payload, response port, raw continuation and current-state dependencies, including a suspended prefix. |
| Bind | Lift the original ordered continuation image. A pending Request retains `k >>= suffix`, including the unreached suffix's static contract. |
| Delay / closure | Immediate construction is inert; retain the entire latent relation and captured roots at their original typed paths. |
| Call | Lift `J_f >>= ExecuteCallable(actual_f,Delay(J_a))` with actual entry, receiver/receipt, body and designated consumer. Native operation return is followed by its original result consumer. |
| Scoped binder / renaming | Keep one binder at its original position; all incident operands and evidence move by the same legal map. |

An empty **membership relation** still needs an independently typed contract
certificate if it is a possible leaf. K-Empty is the zero-arity K-Leaf
instance: it introduces an original contract whose complete relation is
empty, without deriving source/world/owner existence from vacuous coverage.
The original owner introduction below is still required. A divergent
computation with admitted pending prefixes is not an empty relation.

**K-Owner.** For this source, the precise slot/position premise to be proved
is:

```text
Resolve(u_f,d_f)   Capture(step,d_f,R)   SharedContract(d_f,R,sigma_apply)
UnannotatedFormal(d_f)   SeedOrigin(k,d_f,sigma_apply)
ProtectedVarAt(k,d_f,sigma_step,u_f)
SourceUpperUse(u_f,d_f,U,sigma_step)
TypedOutputCorrespondence(U,outEff(U),p0; original scope tree,xi)
---------------------------------------------------------------- K-Owner
exists original s,o. s in Slots_orig(beta), beta=(d_f,R),
  Own_orig(beta,s,u_f,p0,o;X).
```

`TypedOutputCorrespondence` is an independently justified original path
premise, not the equation `s=p0`. The rule asserts neither uniqueness nor a
slot count. Its own-upper origin is separate from pre-existing provider
ownership. For a known external Name without this formal seed, this rule
does not fire; provider-owned evidence can still enter through K-Leaf.

**K-Incidence.** The final joint introduction, not a label cast, is:

```text
Own_orig(beta,s,u,p0,o;X)
Contrib_orig(c,rho_U;X) and Emb_orig(L(E),c,v;X)
TypedOriginalSourceImage(E,u,rho_U;X)
--------------------------------------------------------- K-Incidence
exists a in I_orig(X). Inc_orig(a,beta,s,p0,u,c;X)
  with original owner o, original contribution evidence v,
  and the exact original source-stage/view map.
```

Its local compatibility law is required explicitly:

```text
Inc_orig(a,...,c;X) and CMem_orig(c,y,w;X)
  and OriginalFamilyProjection(E,y,z;X)
  => Cover_orig(a,z;X).
```

This is an original coverage/introduction law. It does not define
`Cover_orig` to be `CMem_orig`. Source-relative incidence in `y` is retained:
a complete Call's callee prefix is not automatically an event at the
formal receiver's upper `p0`. Static coverage cannot replace actual Observe,
same-view Receive and liveness premises needed to mark a concrete event.

### 3.3 Candidate exhaustive licensing sequents

Each original constructor above must provide a forward original licensing
derivation at identical coordinates. Its attachment proof retains its actual
origin; `Lic_orig` is not defined as attachment. More precisely, K-Attach(r)
must prove the original source-constructor correspondence from that arm's
resolved source/contract origin, original owner/contribution introduction,
and already attached child premises. Its conclusion is an original Attach
derivation retaining the same local kernel evidence. K-Lic-Intro(r) takes
that actual Attach constructor to its original licensing constructor. These
are additional original rule obligations, rather than definitions of Attach
or Lic. For inversion require this **separate** last-rule elimination sequent:

```text
ell : Lic_orig(X,beta,s,p,c)
---------------------------------------------------------------- K-Lic-Elim
exists original last-rule arm r, exact premises ell_i and certificate m.
  OriginalLicRule_r(ell_i,m;ell)
  and r is OwnUpper | ProviderOrigin | AnnotationOrigin | MixedUse
       | CertifiedTransport | ConservativeContract | RegisteredReference
  and Origin_r is the original resolved source/contract origin
  and the original owner/contribution premises of K-Attach(r)
      are recovered with this same ell, beta,s,p,c, X and kernel evidence.
```

The listed sum is a candidate exhaustive rule list. An actual original rule
outside it is a falsifier of that exhaustivity hypothesis; the list is not a
definition erasing unknown licenses. Base elimination must reach the original
primitive kernel, including conservative contract origins. An annotation
arm recovers its exact source boundary and permission; it does not imply that
removal occurred. A mixed-use arm recovers all correlated demands. A
transport arm recovers the original input witness and legal joint map,
including its independent admission certificate and Generalize eligibility.

For a finite licensing derivation, induction on its height supplies child
attachments; apply K-Attach(r) to the recovered actual origin and kernel
premises to prove the inverse. In the forward direction K-Lic-Intro(r)
provides each corresponding original license. None of those local rules
may take their own target attachment as a premise. If the actual
licensing relation has another recursion principle, its own elimination
theorem is needed; it cannot be replaced by this finite-derivation claim.

## 4. Constructive assembly and all-witness theorem

**Theorem (conditional whole-contract lifting).** Fix one original scope
tree and assignment `X`, independent admission and descriptor meanings, a
finite typed positive relation presentation `E`, complete local typing, and
proved K-Leaf/K-Image laws for its actual clauses. Suppose K-Owner and
K-Incidence hold for its designated source upper. Then construct one
original `a_E in I_orig(X)` incident at that upper and covering all
`F_E(X)`. If the K-Image witness back laws, K-Attach/K-Lic-Intro and
K-Lic-Elim also hold, every
original licensed witness in the declared source/contract envelope has an
attachment/origin representation retaining that very witness. No original
licensed witness is discarded by the construction.

**Construction.** Traverse the finite presentation's acyclic constructor
dependencies. At a primitive apply K-Leaf. At each constructor apply its
K-Image instance to the entire child contracts, producing one parent
contract before any observation is selected. Keep all child alternatives as
evidence fibers. K-Owner supplies an actual original `s,o`; K-Incidence
then produces the original `a_E`. Neither `c_E=L(E)` nor `s=p0` is used.

**Coverage proof.** Independently induct on a finite complete membership
derivation of `R_E`. At a primitive K-Leaf embeds its actual local witness.
For a constructor, induction supplies child original membership evidence;
K-Image supplies the original whole image with the same compatible tuple,
scopes and ordered operands. Union retains the chosen branch evidence;
the **parent contract** was constructed to contain both branches, so the
resulting `c_E` and `a_E` are independent of that choice. Bind preserves
Request's pending suffix, current resumed state and unreached latent
contracts. Closure/delay keep latent contracts, and later finite future
uses apply the same image law. The final original compatibility law gives
`Cover_orig(a_E,z;X)` for arbitrary `z in F_E(X)`.

Thus the quantifiers are:

```text
exists fixed original c_E,a_E.
  forall admitted z in F_E(X). Cover_orig(a_E,z;X).
```

They are not `forall z exists c_z,a_z`. A finite certificate denotes all
finite histories; it does not enumerate a fixed number of histories. An
empty family still obtains `a_E` from K-Owner/K-Incidence and a typed empty
contract, rather than from an empty universal statement.

**Witness preservation proof.** Structural forward embedding retains each
local evidence alternative. Structural back embedding recovers those exact
alternatives for represented original contracts. For an arbitrary original
license, K-Lic-Elim chooses its actual last rule; invert its exact primitive
origin or legal transport and recurse on its licensing premises. The result
retains the input `ell`, rather than substituting a canonical one. The
original relation is never changed. Existential assembly alone has no such
inverse: the predecessor's `a0/w0,a1/w1` equal-observation witness remains
a counterexample if K-Lic-Elim or witness back laws are omitted.

**Representation independence.** Let a proof presentation be reencoded by a
bijective map preserving the original typed maps, primitive evidence,
constructor tags and every active operand. Conjugate each certificate and
each embedding relation by that one map. Induction yields the same original
contract/incidence judgments and inverse witness relation. This gives
invariance under proof representation; it does not assert unique original
contracts or that an extensional quotient preserves original evidence.
A noninjective canonicalization requires its own witness-level certificate.

**Recursion boundary.** A finite acyclic graph covers the exact selected
source skeleton. Arbitrary monomorphic recursive presentations require an
additional original **simultaneous contract** introduction and finite
membership-unfolding law at the registered roots. Finite observation
derivation induction alone cannot introduce that static knot. Such a rule
is not assumed for this result or smuggled in as K-Image.

This theorem discharges the *candidate calculus's* compositional P3 proof
from local original lifting laws. It does not discharge the DAG's
ORIGINAL_ASSOC or SIG_RULES until those laws are original-rule theorems.
Likewise its licensing conclusion is conditional, not a closed LIC_INVERT.

## 5. The exact source cut and remaining additional sequents

For the selected `f x`, assemble the already resolved/typed Name roots and
the inert argument through Return, Delay and complete Call K-Image instances.
The latent inner lambda retains that certificate and the same `f` capture.
The surrounding binding returns `step`; it does not cause Call membership
to become immediate block execution. K-Owner is applied to the static body
exposure even if the returned closure is never invoked. Static association
does not depend on an execution event.

The exact additional original introduction to be established at this cut is
the composition of the displayed K-Owner and K-Incidence sequents with the
Call lifting law, with no semantic relabeling:

```text
resolved/captured outer formal and shared root (d_f,R)
original seed-at-exposure, original upper U and typed p0 correspondence
independent original Name/argument/provider contracts and complete Hcall
K-Leaf and K-Image(Return,Delay,Call) on their original typed maps
---------------------------------------------------------------- Own-Call-Lift
exists original s,c,a,o,v.
  s in Slots_orig((d_f,R))
  and Own_orig((d_f,R),s,u_f,p0,o;X)
  and Contrib_orig(c,rho_U;X) and Emb_orig(L(J_fx),c,v;X)
  and a in I_orig(X), Inc_orig(a,(d_f,R),s,p0,u_f,c;X)
  and forall z in F_C(X). Cover_orig(a,z;X).
```

The new proposal does **not** assume the bottom `forall` as an input.
Its proof follows from the local original contract constructors and the
explicit original incidence/coverage compatibility law. Its unresolved
semantic inputs are now the exact K-Owner sequent, the original
contribution lift of the full invocation image, and K-Incidence's joint
coherence law. P4 additionally needs K-Lic-Elim over the actual original
rules. None is obtained from §6.1 allocation coverage, which retains the
non-coverage kernel, or from C-realization, which consumes it.

These are more specific than “needs a source rule”: they identify source
premises, original output sorts, binder locations, the universal family to
be covered, and the exact whole-tuple laws for the proposed constructors.
Original local contribution operations could falsify the proposal. For
example, if original union can only retain separate association contracts
and has no jointly incident parent contract, this K-Image(Union) cannot be
derived. If original incidence restricts a contract to actual events, its
coverage law fails on static never-invoked exposure or pending prefixes.
These are candidate-law falsifiers, not established Yulang facts.

### 5.1 Direct attack on the smallest original introduction

The displayed names cannot provide semantics by themselves. The following
is a more concrete candidate **Call-contract constructor rule**, sufficient
for the selected K-Image(Call)/K-Incidence cut if it is an actual original
rule. It uses existing original contribution objects in its conclusion;
the mathematical relation constructed below is not one of those objects.

Take the original source environment with resolved `d_f,d_x`. Independently
interpret the provider assigned to `d_f`, with its actual callable role,
entry, body/native invocation and declared result consumer. Independently
interpret `d_x`'s rebound Value interface. Let the ordinary Name rules yield:

```text
Name_f(C) = Return(actual_provider_of(d_f),C)
Name_x(C) = Return(actual_rebound_value_of(d_x),C).
```

These are the exact local relation images, conditional on lookup adequacy.
Both preserve all dependent roots of the resolved lexical environment. No
entry effect of `step` is substituted for `Name_x`.

Construct the following entire relation `R_fx` over the existing complete
observation carrier, at the original `X`; its denotation is specified by
the actual source rules, rather than the word “contribution”:

```text
Name_f >>= ((actual_f,C) =>
  EnterActualReceiverAndReceipt(actual_f,Delay(Name_x),C) ;
  Entry_actual_f ; BodyOrNativeInvocation_actual_f ;
  DeclaredResultConsumer_actual_f ; InvocationReturn)
```

For a closure Value entry, `Entry` forces that one delayed `Name_x`,
rebinds its returned value at the original result path in the current state,
then enters the body. Retained entry instead binds the same carrier and
does not force it; independently explicit body consumers remain present.
For an operation, native invocation can return a request thunk; the declared
result consumer runs that thunk after native return at the source-designated
port. It is not absorbed into the native body.

Every sequencing edge has the original full equations:

```text
Return(v,C) >>= S = S(v,C)
Request(q,C,k) >>= S = Request(q,C, (r,C') => k(r,C') >>= S).
```

Thus the relation includes original pending prefixes with the same request
and raw handle, all compatible typed responses/current resumed states,
and the full suffix including rebind, body and consumer. A returned latent
provider is retained as that provider with its complete future-use relation;
it is not recursively executed. No timeout or absence of return discards
those alternatives. This is the existing complete Call construction, not
an outward row union. Primitive conservative alternatives enter through
the independently interpreted provider relation; a source execution is not
a premise for each such alternative.

Do not equate this source argument diagonal with the complete inlet domain
of `U`. For the stronger candidate, let `R_U_all` be the same complete
invocation equation evaluated with the **whole argument carrier t supplied
by an arbitrary independently typed compatible punctured caller context**,
in place of `Delay(Name_x)`. The callable is the actual provider placed in
that callable hole. Other bindings/imports, original owner/typed paths,
scope, authority and joint dependencies stay independently valid at the
same `X`. Contexts need not be reached by this program. Typed responses,
original raw handles/current states, and future uses at actually returned
provider ports extend those challenges independently of membership or `Q`.
Those are the approved inlet-domain conditions, not a domain defined by
the construction's success. Their complete semantic clauses are retained
as independent premises. The source `R_fx` is a coherent subfamily of this
parameterized whole-inlet relation when its actual filling is independently
admitted. No such filling's inhabitance is proved here.

The exact constructor proposal is:

```text
original static slot s and owner/upper/output-path evidence o at (d_f,R,u_f,p0)
the independent lexical/provider contracts just described
the whole R_U_all construction with original receiver/receipt/consumer maps
independent complete Call typing of every independently admitted full tuple
original scope/authority/guarantee equations and all joint K,D retained
---------------------------------------------------------------- OC-Call-Intro [CANDIDATE]
exists original contribution c and original kernel witness a.
  the complete contract of c is R_U_all with its original evidence fibers,
  c has the original U output-contract type at p0,
  a in I_orig(X) owns (beta=(d_f,R),s,p0,c) through u_f,
  its original source license retains o and every provider evidence arm,
  and the original coverage law validates every corresponding full tuple.
```

“The complete contract of c is R_U_all” is a substantive candidate semantic
law: a map from the original contribution domain to whole observation and
evidence families takes some original `c` to this explicit relation. It
does not set `c=R_U_all`, allocate a fresh replacement contribution label, or
define the original contribution domain to be these families. It specifies
the required **original-domain closure under the complete invocation image**.
It is not a proposal that all production membership equal source execution:
`R_U_all` uses the full independently interpreted provider bound and broad
whole-carrier inlet domain, and
any additional original production-root alternatives require their actual
contract/lifting cases. Source-only `P_ref` cannot replace that bound.

**Attempted derivation.** Name/result rules construct the two returning
relations and preserve the original provider root. Delay constructs the
inert argument. The actual producer and Bind equations construct the entire
`R_fx`, including its pending/future portions. Granting Hcall establishes
its ordinary descriptor typing independently of attachment. Existing
source-contract conjunction, union and image clauses can therefore denote
`R_fx`; they can also retain its original constraints.

Uniformly replacing the source argument by each independently admitted
whole carrier gives the parameterized `R_U_all` under the same complete
Call laws. This step retains the broad domain as a premise; it neither
derives that domain nor restricts it to `Delay(Name_x)`. Grant Hcall on that
entire domain, not just on the source diagonal.

The derivation then has a typed relation, not an object of the original
contribution domain. The image equations give no surjectivity of the
original contribution interpretation at `R_U_all`. No inspected original
owner/kernel constructor has a conclusion providing that preimage or the
joint original source incidence. The exact **irreducible added semantic
clause for this candidate** is therefore: the original source-owned
contribution interpretation admits the full typed invocation image at
this static exposure and licenses it with its exact original owner and
provider evidence. If original complete contributions already admit that
closure, its proof eliminates the added clause. If they do not, adopting
OC-Call-Intro would change semantics and must not be treated as derivation.

The separate slot premise is also not proved by the relation equations.
FVIEW requires `beta=(d_f,R)` and static identity to persist; its text does
not exhibit a constructor inhabiting an original `s in Slots(beta)` with
the typed output path and joint owner evidence. The precise remaining
slot sequent is K-Owner, now with an explicit same-scope seed-at-exposure
premise; the package does not automatically transport a declaration seed
into an arbitrary exposure. An independently supplied provider contract at
Name lookup establishes neither that own-upper slot nor a new seed.

For K-Leaf(Name), the smallest valid existing derivation merely copies the
resolved original **provider descriptor** and its original evidence. It can
copy an original contribution if that lexical contract already supplies one,
but source-contracts' generic primitive contract input does not identify
every descriptor with an original contribution object. The exact added
primitive law would be that each independently typed provider-contract leaf
has an original contribution realization retaining each of its existing
local evidence alternatives. Name copying alone cannot supply this law.

This direct attack reaches OC-Call-Intro's original-domain closure and
source-owner coherence, rather than stopping at the notation `Emb_orig`.
It closes no leaf and supplies no numerical count of new conditional gates.

## 6. Compatibility/falsification against the admitted-source envelope

The hard test is the approved complete `Rel_C` basis on the same original
fiber and every independently typed compatible punctured caller context.
The package does not restrict that context domain to this program's reached
uses, returning histories, source-reference members or a finite probe set.

| Envelope feature | Candidate requirement / attempted falsification |
| --- | --- |
| Exact captured nested source | Closure/delay laws preserve `d_f,R` and latent `J_fx`; Return does not activate it. An ownership rule depending on invocation is incompatible with static exposure. |
| Divergence and suspension | Contract lifting retains complete pending prefixes and unreached suffix contracts. K-Empty is inapplicable merely because no result returns. |
| Arbitrary finite future uses/resumption | Membership proof induction uses original response/raw handle/current-state/future provider evidence, without a fixed history cap. No admitted context existence is inferred. |
| Value versus retained entry | Call lifting uses the actual producer entry. Ordinary x's source role cannot rewrite a supplied callable into Pure; force schedules remain source-owned. |
| Callee prefix versus receiver view | Whole contribution retains stage maps. K-Incidence is not a blanket event-protection rule for all Call observations. |
| Upper and provider protection | Own K-Owner arm introduces only its selected upper occurrence. Provider evidence enters independently and survives. |
| Option 2 extras | Primitive conservative contracts and their full hard guards are lifted as contracts, with no source-execution requirement. A source-only original lift would fail this envelope. |
| Annotation/generalized/imported arms | K-Lic-Elim must reach original boundary and contract origin, preserving permission versus removal and independent Generalize eligibility. Not discharged by this source example. |
| Mixed use and scope correlation | All required uses live on one whole tuple and original scope tree. Local assembly that combines incompatible `xi` or typed maps is rejected. |

No contradiction with these fixed decisions is demonstrated by the candidate
laws. This is a compatibility screen, not a proof that an original
kernel satisfying the laws exists. In particular no two complete semantics
of the same admitted original source have been constructed. There is no
basis here for asking the user to choose an acceptance outcome.

The deterministic probe supplies 64 whole-evidence union cases, 64
whole-tuple conjunction cases, eight bijective transports, two directional
provider-mark cases and one exact nested inert-return/capture record. Twelve
named mutations reject changed `xi`, scope, capture and upper; observation
canonicalization; pointwise-only family selection; lost pending suffix;
lost future port; executing latent return; marginal recombination; an extra
outside the hard guard; and replacing original licenses by one assembly
image. Those witnesses concern the explicit candidate algebra. None is a
typed admitted-source counterexample or an implementation comparison.

## 7. Dependency freeze, verification, and omissions

Direct operating and semantic dependencies are hashed below. Read-only HEAD
resolution matched the assigned baseline. Inputs were read from the shared
working tree; the primary owns comparison to the pinned Git objects and
dependency revalidation at integration. No Git mutation, child, Cargo,
compiler edit, question-board write or production test was performed.

Verification command: `prlimit --as=1073741824 timeout 60s python3
tools/research_successor_original_kernel_round2.py`. Exactly one Python
process is authorized/run, with a 60-second wall limit and 1 GiB address-space
limit, and no files/output shards written by the probe. Counts/results and
measured resources: exit 0; 64 union and 64 conjunction cases, eight
transports, two directional cases, one nested-source record and all twelve
named mutations rejected; calculation 0.000567 seconds, peak RSS 9,984 KiB.
No timeout, uncovered range or second Python process. The attempted
read-only `ps` resource inventory failed with a container library error;
the deliberately tiny probe is bounded and spawns no process itself.

Source reads used bounded `rg`, `cat`, `sed`; large initial aggregate reads
were truncated and decisive constructor, coverage, complete entry, DAG and
predecessor windows were reread. No global rule absence claim is made.
Integrity checks include dependency SHA-256 recheck and leased-path
whitespace inspection. Producer checks do not provide independent review.
All thirty recorded dependencies passed `sha256sum -c` at freeze; no
dependency changed from the recorded snapshot. The probe hash matched its
executed version. Whitespace inspection on both leases found no trailing
spaces or tab characters. These checks do not assert baseline Git-blob
equality; the primary retains that integration check.

Omitted: deriving actual complete Hcall, primitive lifting certificates,
original owner and joint incidence laws, exhaustive original licensing,
arbitrary annotation/mixed/recursive contract realization, all-world initial
inhabitance, production `Sat_A`/`Adm_A` clauses and both inclusions,
source/parser/HIR/compiler acceptance, soundness and principality. The finite
checker uses supplied candidate laws; it is not independent semantics.

| Frozen dependency | SHA-256 |
| --- | --- |
| `AGENTS.md` | `c5ab6ebf0d72fda4c025abc3a0ec9d57c9015a0c8e4ba65900ed385fb62fb9b3` |
| `.codex/config.toml` | `112cefc1ff5a253ea04026561ea67668dc0d18b8269a0cfa51702ab9d6d52f01` |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `tasks/current.md` | `f7fc1bee2e370ec1174c416a737db9f2112f55eebee8fc7c93e73f4929ca2d82` |
| `tasks/research-lab.md` | `d8794543008221be430c3b676929b8601fb4534799fc67856e99ad140da0975d` |
| `notes/design/INDEX.md` | `222eb6613c51e175de81be32172017e4f5fddcac18119716bdf675f841f3bbd2` |
| `notes/theory/successor-proof-obligations.md` | `18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/progress/2026-10-08-original-call-kernel-contract-candidate.md` | `b401a3331ab96eb2668fd7d9bb7ec9488482c0550570f24ab3c29e071320246f` |
| `notes/progress/2026-10-09-original-assoc-p2-constructor-attack.md` | `8561d36a2e82c19247c5c73bafc903222e3636c49e1ffd7f9a0e8ce24636a78f` |
| `notes/progress/2026-10-09-original-association-uniform-witness-falsifier.md` | `ab8cf6c40f221e4a33d5eb40dbe612a42bd04cb9cbbe8ef4b2e828a4e1658d74` |
| `notes/progress/2026-10-07-successor-source-association-falsification.md` | `09a4aee423985c03f1365574e1d4572e67cc6b2f3f3c25fa747b711bbe304738` |
| `notes/progress/2026-10-06-attach-law-construction-attempt.md` | `b94e829e06027c2bd4cc2f0dbf4a33dc954aa10ee058fbc4918da75ad151a241` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-denotation/receipt.md` | `8654359c41d2bf4871904d017d0282155d8763496986a3254405a1220318708b` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `questions/2026-10-05-production-function-bound-membership/receipt.md` | `f69a924b52e0cfb198df62a33e7e5c358ee1d0799ecf7c16cf32b9f8cb2f7e98` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |
| `questions/2026-10-05-production-function-inlet-context-domain/receipt.md` | `a952c4588f6020ba1c51f69c623bf12ef695d73fe086496bf6ecdeee37450021` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |

Probe freeze SHA-256:
`c79424528080abc0ac1580d64ea62222964dde6edee44b81bd28adcd459cb0f3`.

## 8. Commit packet

- Exact leased paths: this note and `tools/research_successor_original_kernel_round2.py`.
- Baseline SHA: `ad514061de2792c374a4b5c224dff7f4772906e8`.
- Claim/review status: unreviewed conditional local-rule construction and
  finite candidate consistency evidence; no gate closure or adoption.
- Changed dependency hashes: none relative to the frozen table; thirty
  successful hash rechecks. Baseline-object equality remains unverified by
  this producer.
- Proposed checkpoint message: `research: construct whole-contract original kernel lift candidate`.
- Shared records deferred to primary: optionally replace the opaque P2/P3
  candidate frontier description by the explicit K-Owner/K-Image/K-Incidence
  and K-Attach/K-Lic-Intro/K-Lic-Elim obligations; retain all existing open
  DAG statuses. OC-Call-Intro explicitly exposes the whole-inlet invocation
  image as the unresolved original contribution-domain closure clause. No
  authority, question, production or test-contract change is proposed.
- Review falsifier: exhibit an actual original-kernel rule or admitted source
  envelope whose contribution constructor lacks whole-family closure,
  cannot inhabit the original owned slot at this source exposure, loses a
  same-observation license witness, or changes the original admission domain.

Producer writes stop at the frozen handoff; independent review belongs to
the primary's separately assigned reviewer.
